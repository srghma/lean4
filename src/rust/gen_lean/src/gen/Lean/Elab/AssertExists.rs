// Lean compiler output
// Module: Lean.Elab.AssertExists
// Imports: Lean.Elab.Command
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr, lean_nat_sub,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_string_dec_lt,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Bool::l_Bool_instDecidableLt;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    l_Lean_Elab_Command_liftCoreM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_allImportedModuleNames, l_Lean_Environment_contains,
    l_Lean_Environment_findConstVal_x3f, l_Lean_Environment_getModuleIdx_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_instInhabitedModuleData_default,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_joinSep,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Trace::{l_Lean_checkEmoji, l_Lean_crossEmoji};
use crate::r#gen::Std::Data::HashSet::Basic::l_Std_HashSet_instInhabited;
pub static l_Lean_Environment_importPath___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Environment_importPath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Environment_importPath___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_instBEqAssertExists___closed__0_value:
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
    m_fun: l_Lean_Elab_Command_instBEqAssertExists_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Command_instBEqAssertExists___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_instBEqAssertExists___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Command_instBEqAssertExists: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_instBEqAssertExists___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0: u64 = 0;
pub static l_Lean_Elab_Command_instHashableAssertExists___closed__0_value:
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
    m_fun: l_Lean_Elab_Command_instHashableAssertExists_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Command_instHashableAssertExists___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_instHashableAssertExists___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Command_instHashableAssertExists: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_instHashableAssertExists___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 115, 115, 101, 114, 116, 69, 120, 105, 115, 116, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13267666777536315134 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value: leanh::LeanCtorObject<7> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Command_assertExistsExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_getSortedAssertExists___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_getSortedAssertExists___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [10, 32, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 98, 121, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_importPathMessage___closed__0_value: leanh::LeanStringObject<
    35,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        10, 32, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101,
        100, 32, 98, 121, 32, 116, 104, 105, 115, 32, 102, 105, 108, 101, 46, 0,
    ],
};
static mut l_Lean_Elab_Command_importPathMessage___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_importPathMessage___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_importPathMessage___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_importPathMessage___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabImportPath___closed__0_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 0],
};
static mut l_Lean_Elab_Command_elabImportPath___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabImportPath___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabImportPath___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabImportPath___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabImportPath___closed__2_value: leanh::LeanStringObject<
    18,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 118, 105, 97, 10, 0,
    ],
};
static mut l_Lean_Elab_Command_elabImportPath___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabImportPath___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabImportPath___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabImportPath___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabImportPath___closed__4_value: leanh::LeanStringObject<
    26,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        32, 105, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 32, 116, 104, 105, 115,
        32, 102, 105, 108, 101, 46, 0,
    ],
};
static mut l_Lean_Elab_Command_elabImportPath___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabImportPath___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabImportPath___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabImportPath___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabImportPath___closed__6_value: leanh::LeanStringObject<
    14,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 39, 0],
};
static mut l_Lean_Elab_Command_elabImportPath___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabImportPath___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabImportPath___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabImportPath___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabImportPath___closed__8_value: leanh::LeanStringObject<
    19,
> = leanh::LeanStringObject {
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
        39, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 115, 99, 111, 112, 101, 46, 0,
    ],
};
static mut l_Lean_Elab_Command_elabImportPath___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabImportPath___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabImportPath___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabImportPath___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 109, 112, 111, 114, 116, 80, 97, 116, 104, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__1_value) as *mut leanh::LeanObject,662811328248324715 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 73, 109, 112, 111, 114, 116, 80, 97, 116, 104, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__3_value) as *mut leanh::LeanObject,10488056670740370564 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0_value: leanh::LeanStringObject<248> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 248, m_capacity: 248, m_length: 247, m_data: [96, 35, 105, 109, 112, 111, 114, 116, 95, 112, 97, 116, 104, 32, 70, 111, 111, 96, 32, 112, 114, 105, 110, 116, 115, 32, 116, 104, 101, 32, 116, 114, 97, 110, 115, 105, 116, 105, 118, 101, 32, 105, 109, 112, 111, 114, 116, 32, 99, 104, 97, 105, 110, 32, 116, 104, 97, 116, 32, 98, 114, 105, 110, 103, 115, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 70, 111, 111, 96, 10, 105, 110, 116, 111, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 102, 105, 108, 101, 39, 115, 32, 115, 99, 111, 112, 101, 46, 10, 10, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 117, 110, 100, 101, 114, 115, 116, 97, 110, 100, 105, 110, 103, 32, 119, 104, 121, 32, 97, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 105, 115, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 44, 10, 101, 115, 112, 101, 99, 105, 97, 108, 108, 121, 32, 119, 104, 101, 110, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105, 101, 115, 46, 10, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0_value: leanh::LeanStringObject<220> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 220, m_capacity: 220, m_length: 219, m_data: [10, 10, 84, 104, 101, 115, 101, 32, 105, 110, 118, 97, 114, 105, 97, 110, 116, 115, 32, 97, 114, 101, 32, 109, 97, 105, 110, 116, 97, 105, 110, 101, 100, 32, 98, 121, 32, 96, 97, 115, 115, 101, 114, 116, 95, 110, 111, 116, 95, 101, 120, 105, 115, 116, 115, 96, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 115, 44, 32, 97, 110, 100, 32, 101, 120, 105, 115, 116, 32, 105, 110, 32, 111, 114, 100, 101, 114, 32, 116, 111, 32, 101, 110, 115, 117, 114, 101, 32, 116, 104, 97, 116, 32, 34, 99, 111, 109, 112, 108, 105, 99, 97, 116, 101, 100, 34, 32, 112, 97, 114, 116, 115, 32, 111, 102, 32, 116, 104, 101, 32, 108, 105, 98, 114, 97, 114, 121, 32, 97, 114, 101, 32, 110, 111, 116, 32, 97, 99, 99, 105, 100, 101, 110, 116, 97, 108, 108, 121, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 100, 32, 97, 115, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105, 101, 115, 32, 111, 102, 32, 34, 115, 105, 109, 112, 108, 101, 34, 32, 112, 97, 114, 116, 115, 32, 111, 102, 32, 116, 104, 101, 32, 108, 105, 98, 114, 97, 114, 121, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2_value: leanh::LeanStringObject<63> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 108, 108, 111, 119, 101, 100, 32, 116, 111, 32, 98, 101, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 98, 121, 32, 116, 104, 105, 115, 32, 102, 105, 108, 101, 46, 10, 73, 116, 32, 105, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 105, 110, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 115, 115, 101, 114, 116, 78, 111, 116, 69, 120, 105, 115, 116, 115, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__0_value) as *mut leanh::LeanObject,14421106859637541903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 108, 97, 98, 65, 115, 115, 101, 114, 116, 78, 111, 116, 69, 120, 105, 115, 116, 115, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__2_value) as *mut leanh::LeanObject,1842914149555460378 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0_value: leanh::LeanStringObject<822> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 822, m_capacity: 822, m_length: 807, m_data: [96, 97, 115, 115, 101, 114, 116, 95, 110, 111, 116, 95, 101, 120, 105, 115, 116, 115, 32, 100, 226, 130, 129, 32, 100, 226, 130, 130, 32, 46, 46, 46, 32, 100, 226, 130, 153, 96, 32, 105, 115, 32, 97, 32, 99, 111, 109, 109, 97, 110, 100, 32, 116, 104, 97, 116, 32, 97, 115, 115, 101, 114, 116, 115, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 110, 97, 109, 101, 100, 10, 96, 100, 226, 130, 129, 32, 100, 226, 130, 130, 32, 46, 46, 46, 32, 100, 226, 130, 153, 96, 32, 42, 100, 111, 32, 110, 111, 116, 32, 101, 120, 105, 115, 116, 42, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 105, 109, 112, 111, 114, 116, 32, 115, 99, 111, 112, 101, 46, 10, 10, 66, 101, 32, 99, 97, 114, 101, 102, 117, 108, 32, 116, 111, 32, 117, 115, 101, 32, 110, 97, 109, 101, 115, 32, 40, 101, 46, 103, 46, 32, 96, 82, 97, 116, 96, 41, 32, 114, 97, 116, 104, 101, 114, 32, 116, 104, 97, 110, 32, 110, 111, 116, 97, 116, 105, 111, 110, 115, 32, 40, 101, 46, 103, 46, 32, 96, 226, 132, 154, 96, 41, 46, 10, 10, 73, 116, 32, 109, 97, 121, 32, 98, 101, 32, 117, 115, 101, 100, 32, 40, 115, 112, 97, 114, 105, 110, 103, 108, 121, 33, 41, 32, 116, 111, 32, 101, 110, 102, 111, 114, 99, 101, 32, 112, 108, 97, 110, 115, 32, 116, 104, 97, 116, 32, 99, 101, 114, 116, 97, 105, 110, 32, 102, 105, 108, 101, 115, 32, 97, 114, 101, 32, 105, 110, 100, 101, 112, 101, 110, 100, 101, 110, 116, 32, 111, 102, 32, 101, 97, 99, 104, 32, 111, 116, 104, 101, 114, 46, 10, 10, 73, 102, 32, 121, 111, 117, 32, 101, 110, 99, 111, 117, 110, 116, 101, 114, 32, 97, 110, 32, 101, 114, 114, 111, 114, 32, 111, 110, 32, 97, 110, 32, 96, 97, 115, 115, 101, 114, 116, 95, 110, 111, 116, 95, 101, 120, 105, 115, 116, 115, 96, 32, 99, 111, 109, 109, 97, 110, 100, 32, 119, 104, 105, 108, 101, 32, 100, 101, 118, 101, 108, 111, 112, 105, 110, 103, 32, 97, 32, 108, 105, 98, 114, 97, 114, 121, 44, 10, 105, 116, 32, 105, 115, 32, 112, 114, 111, 98, 97, 98, 108, 121, 32, 98, 101, 99, 97, 117, 115, 101, 32, 121, 111, 117, 32, 104, 97, 118, 101, 32, 105, 110, 116, 114, 111, 100, 117, 99, 101, 100, 32, 110, 101, 119, 32, 105, 109, 112, 111, 114, 116, 32, 100, 101, 112, 101, 110, 100, 101, 110, 99, 105, 101, 115, 32, 116, 111, 32, 97, 32, 102, 105, 108, 101, 46, 10, 73, 110, 32, 116, 104, 105, 115, 32, 99, 97, 115, 101, 44, 32, 121, 111, 117, 32, 115, 104, 111, 117, 108, 100, 32, 114, 101, 102, 97, 99, 116, 111, 114, 32, 121, 111, 117, 114, 32, 119, 111, 114, 107, 10, 40, 102, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 32, 98, 121, 32, 99, 114, 101, 97, 116, 105, 110, 103, 32, 110, 101, 119, 32, 102, 105, 108, 101, 115, 32, 114, 97, 116, 104, 101, 114, 32, 116, 104, 97, 110, 32, 97, 100, 100, 105, 110, 103, 32, 105, 109, 112, 111, 114, 116, 115, 32, 116, 111, 32, 101, 120, 105, 115, 116, 105, 110, 103, 32, 102, 105, 108, 101, 115, 41, 46, 10, 89, 111, 117, 32, 115, 104, 111, 117, 108, 100, 32, 42, 110, 111, 116, 42, 32, 100, 101, 108, 101, 116, 101, 32, 116, 104, 101, 32, 96, 97, 115, 115, 101, 114, 116, 95, 110, 111, 116, 95, 101, 120, 105, 115, 116, 115, 96, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 119, 105, 116, 104, 111, 117, 116, 32, 99, 97, 114, 101, 102, 117, 108, 32, 100, 105, 115, 99, 117, 115, 115, 105, 111, 110, 32, 97, 104, 101, 97, 100, 32, 111, 102, 32, 116, 105, 109, 101, 46, 10, 10, 96, 97, 115, 115, 101, 114, 116, 95, 110, 111, 116, 95, 101, 120, 105, 115, 116, 115, 96, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 115, 32, 115, 104, 111, 117, 108, 100, 32, 103, 101, 110, 101, 114, 97, 108, 108, 121, 32, 108, 105, 118, 101, 32, 97, 116, 32, 116, 104, 101, 32, 116, 111, 112, 32, 111, 102, 32, 116, 104, 101, 32, 102, 105, 108, 101, 44, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 100, 111, 99, 46, 10, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [39, 32, 105, 115, 32, 40, 116, 114, 97, 110, 115, 105, 116, 105, 118, 101, 108, 121, 41, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 118, 105, 97, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [97, 115, 115, 101, 114, 116, 78, 111, 116, 73, 109, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__0_value) as *mut leanh::LeanObject,10013208244628196908 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 65, 115, 115, 101, 114, 116, 78, 111, 116, 73, 109, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__2_value) as *mut leanh::LeanObject,7017961480317200931 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0_value: leanh::LeanStringObject<251> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 251, m_capacity: 251, m_length: 232, m_data: [96, 97, 115, 115, 101, 114, 116, 95, 110, 111, 116, 95, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 226, 130, 129, 32, 109, 226, 130, 130, 32, 46, 46, 46, 32, 109, 226, 130, 153, 96, 32, 99, 104, 101, 99, 107, 115, 32, 116, 104, 97, 116, 32, 101, 97, 99, 104, 32, 111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 115, 32, 96, 109, 226, 130, 129, 32, 109, 226, 130, 130, 32, 46, 46, 46, 32, 109, 226, 130, 153, 96, 32, 105, 115, 32, 110, 111, 116, 10, 97, 109, 111, 110, 103, 32, 116, 104, 101, 32, 116, 114, 97, 110, 115, 105, 116, 105, 118, 101, 32, 105, 109, 112, 111, 114, 116, 115, 32, 111, 102, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 102, 105, 108, 101, 46, 10, 10, 84, 104, 101, 32, 99, 111, 109, 109, 97, 110, 100, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 99, 104, 101, 99, 107, 32, 119, 104, 101, 116, 104, 101, 114, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 115, 32, 96, 109, 226, 130, 129, 32, 109, 226, 130, 130, 32, 46, 46, 46, 32, 109, 226, 130, 153, 96, 32, 97, 99, 116, 117, 97, 108, 108, 121, 32, 101, 120, 105, 115, 116, 46, 10, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [39, 32, 40, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [41, 32, 97, 115, 115, 101, 114, 116, 101, 100, 32, 105, 110, 32, 39, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [39, 46, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 111, 100, 117, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCheckAssertions___closed__4_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [45, 45, 45, 0],
};
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCheckAssertions___closed__6_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        32, 109, 101, 97, 110, 115, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116,
        105, 111, 110, 32, 111, 114, 32, 105, 109, 112, 111, 114, 116, 32, 101, 120, 105, 115, 116,
        115, 46, 0,
    ],
};
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCheckAssertions___closed__9_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        32, 109, 101, 97, 110, 115, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116,
        105, 111, 110, 32, 111, 114, 32, 105, 109, 112, 111, 114, 116, 32, 100, 111, 101, 115, 32,
        110, 111, 116, 32, 101, 120, 105, 115, 116, 46, 0,
    ],
};
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCheckAssertions___closed__12_value:
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
    m_data: [10, 0],
};
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCheckAssertions___closed__13_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCheckAssertions___closed__15_value:
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
        78, 111, 32, 97, 115, 115, 101, 114, 116, 105, 111, 110, 115, 32, 109, 97, 100, 101, 46, 0,
    ],
};
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCheckAssertions___closed__16_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__15_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCheckAssertions___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabCheckAssertions___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [99, 104, 101, 99, 107, 65, 115, 115, 101, 114, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17342580262104060118 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__0_value) as *mut leanh::LeanObject,17981410584565439100 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 108, 97, 98, 67, 104, 101, 99, 107, 65, 115, 115, 101, 114, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__2_value) as *mut leanh::LeanObject,13615505730543968110 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0_value: leanh::LeanStringObject<776> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 776, m_capacity: 776, m_length: 772, m_data: [96, 35, 99, 104, 101, 99, 107, 95, 97, 115, 115, 101, 114, 116, 105, 111, 110, 115, 96, 32, 114, 101, 116, 114, 105, 101, 118, 101, 115, 32, 97, 108, 108, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32, 97, 108, 108, 32, 105, 109, 112, 111, 114, 116, 115, 32, 116, 104, 97, 116, 32, 119, 101, 114, 101, 32, 100, 101, 99, 108, 97, 114, 101, 100, 10, 110, 111, 116, 32, 116, 111, 32, 101, 120, 105, 115, 116, 32, 115, 111, 32, 102, 97, 114, 32, 40, 105, 110, 99, 108, 117, 100, 105, 110, 103, 32, 105, 110, 32, 116, 114, 97, 110, 115, 105, 116, 105, 118, 101, 108, 121, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 102, 105, 108, 101, 115, 41, 32, 97, 110, 100, 32, 114, 101, 112, 111, 114, 116, 115, 32, 116, 104, 101, 105, 114, 32, 99, 117, 114, 114, 101, 110, 116, 10, 115, 116, 97, 116, 117, 115, 58, 10, 42, 32, 226, 156, 147, 32, 109, 101, 97, 110, 115, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 114, 32, 105, 109, 112, 111, 114, 116, 32, 101, 120, 105, 115, 116, 115, 44, 10, 42, 32, 195, 151, 32, 109, 101, 97, 110, 115, 32, 116, 104, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 114, 32, 105, 109, 112, 111, 114, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 101, 120, 105, 115, 116, 46, 10, 10, 84, 104, 105, 115, 32, 109, 101, 97, 110, 115, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 101, 120, 112, 101, 99, 116, 97, 116, 105, 111, 110, 32, 105, 115, 32, 116, 104, 97, 116, 32, 97, 108, 108, 32, 99, 104, 101, 99, 107, 115, 32, 42, 115, 117, 99, 99, 101, 101, 100, 42, 32, 98, 121, 32, 116, 104, 101, 32, 116, 105, 109, 101, 32, 96, 35, 99, 104, 101, 99, 107, 95, 97, 115, 115, 101, 114, 116, 105, 111, 110, 115, 96, 10, 105, 115, 32, 117, 115, 101, 100, 44, 32, 116, 121, 112, 105, 99, 97, 108, 108, 121, 32, 111, 110, 99, 101, 32, 97, 108, 108, 32, 111, 102, 32, 116, 104, 101, 32, 108, 105, 98, 114, 97, 114, 121, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 98, 117, 105, 108, 116, 46, 10, 10, 73, 102, 32, 97, 108, 108, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32, 105, 109, 112, 111, 114, 116, 115, 32, 97, 114, 101, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 119, 104, 101, 110, 32, 96, 35, 99, 104, 101, 99, 107, 95, 97, 115, 115, 101, 114, 116, 105, 111, 110, 115, 96, 32, 105, 115, 32, 117, 115, 101, 100, 44, 10, 116, 104, 101, 110, 32, 116, 104, 101, 32, 99, 111, 109, 109, 97, 110, 100, 32, 108, 111, 103, 115, 32, 97, 110, 32, 105, 110, 102, 111, 32, 109, 101, 115, 115, 97, 103, 101, 46, 32, 79, 116, 104, 101, 114, 119, 105, 115, 101, 44, 32, 105, 116, 32, 101, 109, 105, 116, 115, 32, 97, 32, 119, 97, 114, 110, 105, 110, 103, 46, 10, 10, 84, 104, 101, 32, 118, 97, 114, 105, 97, 110, 116, 32, 96, 35, 99, 104, 101, 99, 107, 95, 97, 115, 115, 101, 114, 116, 105, 111, 110, 115, 33, 96, 32, 111, 110, 108, 121, 32, 112, 114, 105, 110, 116, 115, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 47, 105, 109, 112, 111, 114, 116, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 116, 104, 101, 10, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116, 46, 32, 73, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 44, 32, 105, 116, 32, 105, 115, 32, 115, 105, 108, 101, 110, 116, 32, 105, 102, 32, 101, 118, 101, 114, 121, 116, 104, 105, 110, 103, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 44, 32, 109, 97, 107, 105, 110, 103, 32, 105, 116, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 116, 101, 115, 116, 105, 110, 103, 46, 10, 0]};
static mut l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0(
    mut v___x_2134_: *mut leanh::LeanObject,
    mut v_as_2135_: *mut leanh::LeanObject,
    mut v_i_2136_: usize,
    mut v_stop_2137_: usize,
) -> u8 {
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: u8 = 0;
    let mut v___x_2142_: usize = 0;
    let mut v___x_2143_: usize = 0;
    let mut v___x_2145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2138_ = lean_usize_dec_eq(v_i_2136_, v_stop_2137_);
                if v___x_2138_ == 0 {
                    v___x_2139_ = lean_array_uget_borrowed(v_as_2135_, v_i_2136_);
                    v_module_2140_ = leanh::lean_ctor_get(v___x_2139_, 0);
                    v___x_2141_ = lean_name_eq(v_module_2140_, v___x_2134_);
                    if v___x_2141_ == 0 {
                        v___x_2142_ = 1usize;
                        v___x_2143_ = lean_usize_add(v_i_2136_, v___x_2142_);
                        v_i_2136_ = v___x_2143_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2141_;
                    }
                } else {
                    v___x_2145_ = 0;
                    return v___x_2145_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0___boxed(
    mut v___x_2146_: *mut leanh::LeanObject,
    mut v_as_2147_: *mut leanh::LeanObject,
    mut v_i_2148_: *mut leanh::LeanObject,
    mut v_stop_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2150_: usize = 0;
    let mut v_stop_boxed_2151_: usize = 0;
    let mut v_res_2152_: u8 = 0;
    let mut v_r_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2150_ = leanh::lean_unbox_usize(v_i_2148_);
    leanh::lean_dec(v_i_2148_);
    v_stop_boxed_2151_ = leanh::lean_unbox_usize(v_stop_2149_);
    leanh::lean_dec(v_stop_2149_);
    v_res_2152_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0(v___x_2146_, v_as_2147_, v_i_boxed_2150_, v_stop_boxed_2151_);
    leanh::lean_dec_ref(v_as_2147_);
    leanh::lean_dec(v___x_2146_);
    v_r_2153_ = leanh::lean_box((v_res_2152_) as usize);
    return v_r_2153_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(
    mut v_modData_2154_: *mut leanh::LeanObject,
    mut v_modNames_2155_: *mut leanh::LeanObject,
    mut v_range_2156_: *mut leanh::LeanObject,
    mut v_b_2157_: *mut leanh::LeanObject,
    mut v_i_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v_fst_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_imports_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: u8 = 0;
    let mut v___x_2181_: usize = 0;
    let mut v___x_2182_: usize = 0;
    let mut v___x_2183_: u8 = 0;
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_2159_ = leanh::lean_ctor_get(v_range_2156_, 1);
                v_step_2160_ = leanh::lean_ctor_get(v_range_2156_, 2);
                v___x_2165_ = lean_nat_dec_lt(v_i_2158_, v_stop_2159_);
                if v___x_2165_ == 0 {
                    leanh::lean_dec(v_i_2158_);
                    return v_b_2157_;
                } else {
                    v_fst_2166_ = leanh::lean_ctor_get(v_b_2157_, 0);
                    v_snd_2167_ = leanh::lean_ctor_get(v_b_2157_, 1);
                    v_isSharedCheck_2188_ = (!leanh::lean_is_exclusive(v_b_2157_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2169_ = v_b_2157_;
                        v_isShared_2170_ = v_isSharedCheck_2188_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2167_);
                        leanh::lean_inc(v_fst_2166_);
                        leanh::lean_dec(v_b_2157_);
                        v___x_2169_ = leanh::lean_box(0);
                        v_isShared_2170_ = v_isSharedCheck_2188_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2163_ = lean_nat_add(v_i_2158_, v_step_2160_);
                leanh::lean_dec(v_i_2158_);
                v_b_2157_ = v_a_2162_;
                v_i_2158_ = v___x_2163_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2175_ = l_Lean_instInhabitedModuleData_default;
                v___x_2176_ = lean_array_get_borrowed(v___x_2175_, v_modData_2154_, v_i_2158_);
                v_imports_2177_ = leanh::lean_ctor_get(v___x_2176_, 0);
                v___x_2178_ = leanh::lean_unsigned_to_nat(0);
                v___x_2179_ = lean_array_get_size(v_imports_2177_);
                v___x_2180_ = lean_nat_dec_lt(v___x_2178_, v___x_2179_);
                if v___x_2180_ == 0 {
                    state = 3;
                    continue;
                } else {
                    if v___x_2180_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_2181_ = 0usize;
                        v___x_2182_ = lean_usize_of_nat(v___x_2179_);
                        v___x_2183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Environment_importPath_spec__0(v_snd_2167_, v_imports_2177_, v___x_2181_, v___x_2182_);
                        if v___x_2183_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_2169_);
                            leanh::lean_dec(v_snd_2167_);
                            v___x_2184_ = leanh::lean_box(0);
                            v___x_2185_ =
                                lean_array_get_borrowed(v___x_2184_, v_modNames_2155_, v_i_2158_);
                            leanh::lean_inc_n(v___x_2185_, 2);
                            v___x_2186_ = lean_array_push(v_fst_2166_, v___x_2185_);
                            v___x_2187_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2187_, 0, v___x_2186_);
                            leanh::lean_ctor_set(v___x_2187_, 1, v___x_2185_);
                            v_a_2162_ = v___x_2187_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2170_ == 0 {
                    v___x_2173_ = v___x_2169_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_fst_2166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_snd_2167_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_2162_ = v___x_2173_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg___boxed(
    mut v_modData_2189_: *mut leanh::LeanObject,
    mut v_modNames_2190_: *mut leanh::LeanObject,
    mut v_range_2191_: *mut leanh::LeanObject,
    mut v_b_2192_: *mut leanh::LeanObject,
    mut v_i_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2194_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(v_modData_2189_, v_modNames_2190_, v_range_2191_, v_b_2192_, v_i_2193_);
    leanh::lean_dec_ref(v_range_2191_);
    leanh::lean_dec_ref(v_modNames_2190_);
    leanh::lean_dec_ref(v_modData_2189_);
    return v_res_2194_;
}
pub unsafe fn l_Lean_Environment_importPath(
    mut v_env_2197_: *mut leanh::LeanObject,
    mut v_imported_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_moduleData_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = l_Lean_Environment_header(v_env_2197_);
    v_moduleData_2200_ = leanh::lean_ctor_get(v___x_2199_, 6);
    leanh::lean_inc_ref(v_moduleData_2200_);
    v_result_2201_ = l_Lean_Environment_importPath___closed__0;
    v___x_2202_ = l_Lean_Environment_getModuleIdx_x3f(v_env_2197_, v_imported_2198_);
    if leanh::lean_obj_tag(v___x_2202_) == 1 {
        let mut v_val_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_modNames_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2203_ = leanh::lean_ctor_get(v___x_2202_, 0);
        leanh::lean_inc(v_val_2203_);
        leanh::lean_dec_ref_known(v___x_2202_, 1);
        v_modNames_2204_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2199_);
        v___x_2205_ = leanh::lean_unsigned_to_nat(1);
        v___x_2206_ = lean_nat_add(v_val_2203_, v___x_2205_);
        leanh::lean_dec(v_val_2203_);
        v___x_2207_ = lean_array_get_size(v_moduleData_2200_);
        leanh::lean_inc(v___x_2206_);
        v___x_2208_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_2208_, 0, v___x_2206_);
        leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
        leanh::lean_ctor_set(v___x_2208_, 2, v___x_2205_);
        v___x_2209_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2209_, 0, v_result_2201_);
        leanh::lean_ctor_set(v___x_2209_, 1, v_imported_2198_);
        v___x_2210_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(v_moduleData_2200_, v_modNames_2204_, v___x_2208_, v___x_2209_, v___x_2206_);
        leanh::lean_dec_ref_known(v___x_2208_, 3);
        leanh::lean_dec_ref(v_modNames_2204_);
        leanh::lean_dec_ref(v_moduleData_2200_);
        v_fst_2211_ = leanh::lean_ctor_get(v___x_2210_, 0);
        leanh::lean_inc(v_fst_2211_);
        leanh::lean_dec_ref(v___x_2210_);
        return v_fst_2211_;
    } else {
        leanh::lean_dec(v___x_2202_);
        leanh::lean_dec_ref(v_moduleData_2200_);
        leanh::lean_dec_ref(v___x_2199_);
        leanh::lean_dec(v_imported_2198_);
        return v_result_2201_;
    }
}
pub unsafe fn l_Lean_Environment_importPath___boxed(
    mut v_env_2212_: *mut leanh::LeanObject,
    mut v_imported_2213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2214_ = l_Lean_Environment_importPath(v_env_2212_, v_imported_2213_);
    leanh::lean_dec_ref(v_env_2212_);
    return v_res_2214_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1(
    mut v_modData_2215_: *mut leanh::LeanObject,
    mut v_modNames_2216_: *mut leanh::LeanObject,
    mut v_range_2217_: *mut leanh::LeanObject,
    mut v_b_2218_: *mut leanh::LeanObject,
    mut v_i_2219_: *mut leanh::LeanObject,
    mut v_hs_2220_: *mut leanh::LeanObject,
    mut v_hl_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2222_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___redArg(v_modData_2215_, v_modNames_2216_, v_range_2217_, v_b_2218_, v_i_2219_);
    return v___x_2222_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1___boxed(
    mut v_modData_2223_: *mut leanh::LeanObject,
    mut v_modNames_2224_: *mut leanh::LeanObject,
    mut v_range_2225_: *mut leanh::LeanObject,
    mut v_b_2226_: *mut leanh::LeanObject,
    mut v_i_2227_: *mut leanh::LeanObject,
    mut v_hs_2228_: *mut leanh::LeanObject,
    mut v_hl_2229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2230_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Environment_importPath_spec__1(v_modData_2223_, v_modNames_2224_, v_range_2225_, v_b_2226_, v_i_2227_, v_hs_2228_, v_hl_2229_);
    leanh::lean_dec_ref(v_range_2225_);
    leanh::lean_dec_ref(v_modNames_2224_);
    leanh::lean_dec_ref(v_modData_2223_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_Elab_Command_instBEqAssertExists_beq(
    mut v_x_2231_: *mut leanh::LeanObject,
    mut v_x_2232_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_isDecl_2233_: u8 = 0;
    let mut v_givenName_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modName_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDecl_2236_: u8 = 0;
    let mut v_givenName_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modName_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isDecl_2233_ = leanh::lean_ctor_get_uint8(
                    v_x_2231_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_givenName_2234_ = leanh::lean_ctor_get(v_x_2231_, 0);
                v_modName_2235_ = leanh::lean_ctor_get(v_x_2231_, 1);
                v_isDecl_2236_ = leanh::lean_ctor_get_uint8(
                    v_x_2232_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_givenName_2237_ = leanh::lean_ctor_get(v_x_2232_, 0);
                v_modName_2238_ = leanh::lean_ctor_get(v_x_2232_, 1);
                if v_isDecl_2233_ == 0 {
                    if v_isDecl_2236_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v_isDecl_2233_;
                    }
                } else {
                    if v_isDecl_2236_ == 0 {
                        return v_isDecl_2236_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2240_ = lean_name_eq(v_givenName_2234_, v_givenName_2237_);
                if v___x_2240_ == 0 {
                    return v___x_2240_;
                } else {
                    v___x_2241_ = lean_name_eq(v_modName_2235_, v_modName_2238_);
                    return v___x_2241_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_instBEqAssertExists_beq___boxed(
    mut v_x_2242_: *mut leanh::LeanObject,
    mut v_x_2243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2244_: u8 = 0;
    let mut v_r_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2244_ = l_Lean_Elab_Command_instBEqAssertExists_beq(v_x_2242_, v_x_2243_);
    leanh::lean_dec_ref(v_x_2243_);
    leanh::lean_dec_ref(v_x_2242_);
    v_r_2245_ = leanh::lean_box((v_res_2244_) as usize);
    return v_r_2245_;
}
pub unsafe fn _init_l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0() -> u64 {
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u64 = 0;
    v___x_2248_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2249_ = lean_uint64_of_nat(v___x_2248_);
    return v___x_2249_;
}
pub unsafe fn l_Lean_Elab_Command_instHashableAssertExists_hash(
    mut v_x_2250_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_isDecl_2251_: u8 = 0;
    let mut v_givenName_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modName_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2255_: u64 = 0;
    let mut v___y_2256_: u64 = 0;
    let mut v___x_2257_: u64 = 0;
    let mut v___x_2258_: u64 = 0;
    let mut v___x_2259_: u64 = 0;
    let mut v_hash_2260_: u64 = 0;
    let mut v___x_2261_: u64 = 0;
    let mut v___x_2262_: u64 = 0;
    let mut v___y_2264_: u64 = 0;
    let mut v___x_2265_: u64 = 0;
    let mut v___x_2266_: u64 = 0;
    let mut v_hash_2267_: u64 = 0;
    let mut v___x_2268_: u64 = 0;
    let mut v___x_2269_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isDecl_2251_ = leanh::lean_ctor_get_uint8(
                    v_x_2250_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_givenName_2252_ = leanh::lean_ctor_get(v_x_2250_, 0);
                v_modName_2253_ = leanh::lean_ctor_get(v_x_2250_, 1);
                v___x_2262_ = 0u64;
                if v_isDecl_2251_ == 0 {
                    v___x_2268_ = 13u64;
                    v___y_2264_ = v___x_2268_;
                    state = 2;
                    continue;
                } else {
                    v___x_2269_ = 11u64;
                    v___y_2264_ = v___x_2269_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_2257_ = lean_uint64_mix_hash(v___y_2255_, v___y_2256_);
                if leanh::lean_obj_tag(v_modName_2253_) == 0 {
                    v___x_2258_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0_once
                        ),
                        _init_l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0,
                    );
                    v___x_2259_ = lean_uint64_mix_hash(v___x_2257_, v___x_2258_);
                    return v___x_2259_;
                } else {
                    v_hash_2260_ = leanh::lean_ctor_get_uint64(
                        v_modName_2253_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_2261_ = lean_uint64_mix_hash(v___x_2257_, v_hash_2260_);
                    return v___x_2261_;
                }
            }
            2 => {
                v___x_2265_ = lean_uint64_mix_hash(v___x_2262_, v___y_2264_);
                if leanh::lean_obj_tag(v_givenName_2252_) == 0 {
                    v___x_2266_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0_once
                        ),
                        _init_l_Lean_Elab_Command_instHashableAssertExists_hash___closed__0,
                    );
                    v___y_2255_ = v___x_2265_;
                    v___y_2256_ = v___x_2266_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2267_ = leanh::lean_ctor_get_uint64(
                        v_givenName_2252_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2255_ = v___x_2265_;
                    v___y_2256_ = v_hash_2267_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_instHashableAssertExists_hash___boxed(
    mut v_x_2270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2271_: u64 = 0;
    let mut v_r_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2271_ = l_Lean_Elab_Command_instHashableAssertExists_hash(v_x_2270_);
    leanh::lean_dec_ref(v_x_2270_);
    v_r_2272_ = leanh::lean_box_uint64(v_res_2271_);
    return v_r_2272_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(
    mut v_es_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = lean_array_mk(v_es_2275_);
    return v___x_2276_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_a_2277_: *mut leanh::LeanObject,
    mut v_x_2278_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2279_: u8 = 0;
    let mut v_key_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2278_) == 0 {
                    v___x_2279_ = 0;
                    return v___x_2279_;
                } else {
                    v_key_2280_ = leanh::lean_ctor_get(v_x_2278_, 0);
                    v_tail_2281_ = leanh::lean_ctor_get(v_x_2278_, 2);
                    v___x_2282_ =
                        l_Lean_Elab_Command_instBEqAssertExists_beq(v_key_2280_, v_a_2277_);
                    if v___x_2282_ == 0 {
                        v_x_2278_ = v_tail_2281_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2282_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_x_2285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2286_: u8 = 0;
    let mut v_r_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(v_a_2284_, v_x_2285_);
    leanh::lean_dec(v_x_2285_);
    leanh::lean_dec_ref(v_a_2284_);
    v_r_2287_ = leanh::lean_box((v_res_2286_) as usize);
    return v_r_2287_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6___redArg(
    mut v_x_2288_: *mut leanh::LeanObject,
    mut v_x_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2295_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u64 = 0;
    let mut v___x_2298_: u64 = 0;
    let mut v___x_2299_: u64 = 0;
    let mut v_fold_2300_: u64 = 0;
    let mut v___x_2301_: u64 = 0;
    let mut v___x_2302_: u64 = 0;
    let mut v___x_2303_: u64 = 0;
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: usize = 0;
    let mut v___x_2306_: usize = 0;
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: usize = 0;
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2289_) == 0 {
                    return v_x_2288_;
                } else {
                    v_key_2290_ = leanh::lean_ctor_get(v_x_2289_, 0);
                    v_value_2291_ = leanh::lean_ctor_get(v_x_2289_, 1);
                    v_tail_2292_ = leanh::lean_ctor_get(v_x_2289_, 2);
                    v_isSharedCheck_2315_ = (!leanh::lean_is_exclusive(v_x_2289_)) as u8;
                    if v_isSharedCheck_2315_ == 0 {
                        v___x_2294_ = v_x_2289_;
                        v_isShared_2295_ = v_isSharedCheck_2315_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2292_);
                        leanh::lean_inc(v_value_2291_);
                        leanh::lean_inc(v_key_2290_);
                        leanh::lean_dec(v_x_2289_);
                        v___x_2294_ = leanh::lean_box(0);
                        v_isShared_2295_ = v_isSharedCheck_2315_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2296_ = lean_array_get_size(v_x_2288_);
                v___x_2297_ = l_Lean_Elab_Command_instHashableAssertExists_hash(v_key_2290_);
                v___x_2298_ = 32u64;
                v___x_2299_ = lean_uint64_shift_right(v___x_2297_, v___x_2298_);
                v_fold_2300_ = lean_uint64_xor(v___x_2297_, v___x_2299_);
                v___x_2301_ = 16u64;
                v___x_2302_ = lean_uint64_shift_right(v_fold_2300_, v___x_2301_);
                v___x_2303_ = lean_uint64_xor(v_fold_2300_, v___x_2302_);
                v___x_2304_ = lean_uint64_to_usize(v___x_2303_);
                v___x_2305_ = lean_usize_of_nat(v___x_2296_);
                v___x_2306_ = 1usize;
                v___x_2307_ = lean_usize_sub(v___x_2305_, v___x_2306_);
                v___x_2308_ = lean_usize_land(v___x_2304_, v___x_2307_);
                v___x_2309_ = lean_array_uget_borrowed(v_x_2288_, v___x_2308_);
                leanh::lean_inc(v___x_2309_);
                if v_isShared_2295_ == 0 {
                    leanh::lean_ctor_set(v___x_2294_, 2, v___x_2309_);
                    v___x_2311_ = v___x_2294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2314_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_key_2290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_value_2291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 2, v___x_2309_);
                    v___x_2311_ = v_reuseFailAlloc_2314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2312_ = lean_array_uset(v_x_2288_, v___x_2308_, v___x_2311_);
                v_x_2288_ = v___x_2312_;
                v_x_2289_ = v_tail_2292_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5___redArg(
    mut v_i_2316_: *mut leanh::LeanObject,
    mut v_source_2317_: *mut leanh::LeanObject,
    mut v_target_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v_es_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2319_ = lean_array_get_size(v_source_2317_);
                v___x_2320_ = lean_nat_dec_lt(v_i_2316_, v___x_2319_);
                if v___x_2320_ == 0 {
                    leanh::lean_dec_ref(v_source_2317_);
                    leanh::lean_dec(v_i_2316_);
                    return v_target_2318_;
                } else {
                    v_es_2321_ = lean_array_fget(v_source_2317_, v_i_2316_);
                    v___x_2322_ = leanh::lean_box(0);
                    v_source_2323_ = lean_array_fset(v_source_2317_, v_i_2316_, v___x_2322_);
                    v_target_2324_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6___redArg(v_target_2318_, v_es_2321_);
                    v___x_2325_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2326_ = lean_nat_add(v_i_2316_, v___x_2325_);
                    leanh::lean_dec(v_i_2316_);
                    v_i_2316_ = v___x_2326_;
                    v_source_2317_ = v_source_2323_;
                    v_target_2318_ = v_target_2324_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4___redArg(
    mut v_data_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = lean_array_get_size(v_data_2328_);
    v___x_2330_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2331_ = lean_nat_mul(v___x_2329_, v___x_2330_);
    v___x_2332_ = leanh::lean_unsigned_to_nat(0);
    v___x_2333_ = leanh::lean_box(0);
    v___x_2334_ = lean_mk_array(v_nbuckets_2331_, v___x_2333_);
    v___x_2335_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5___redArg(v___x_2332_, v_data_2328_, v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(
    mut v_m_2336_: *mut leanh::LeanObject,
    mut v_a_2337_: *mut leanh::LeanObject,
    mut v_b_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: u64 = 0;
    let mut v___x_2343_: u64 = 0;
    let mut v___x_2344_: u64 = 0;
    let mut v_fold_2345_: u64 = 0;
    let mut v___x_2346_: u64 = 0;
    let mut v___x_2347_: u64 = 0;
    let mut v___x_2348_: u64 = 0;
    let mut v___x_2349_: usize = 0;
    let mut v___x_2350_: usize = 0;
    let mut v___x_2351_: usize = 0;
    let mut v___x_2352_: usize = 0;
    let mut v___x_2353_: usize = 0;
    let mut v_bkt_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: u8 = 0;
    let mut v_val_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v_unused_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2339_ = leanh::lean_ctor_get(v_m_2336_, 0);
                v_buckets_2340_ = leanh::lean_ctor_get(v_m_2336_, 1);
                v___x_2341_ = lean_array_get_size(v_buckets_2340_);
                v___x_2342_ = l_Lean_Elab_Command_instHashableAssertExists_hash(v_a_2337_);
                v___x_2343_ = 32u64;
                v___x_2344_ = lean_uint64_shift_right(v___x_2342_, v___x_2343_);
                v_fold_2345_ = lean_uint64_xor(v___x_2342_, v___x_2344_);
                v___x_2346_ = 16u64;
                v___x_2347_ = lean_uint64_shift_right(v_fold_2345_, v___x_2346_);
                v___x_2348_ = lean_uint64_xor(v_fold_2345_, v___x_2347_);
                v___x_2349_ = lean_uint64_to_usize(v___x_2348_);
                v___x_2350_ = lean_usize_of_nat(v___x_2341_);
                v___x_2351_ = 1usize;
                v___x_2352_ = lean_usize_sub(v___x_2350_, v___x_2351_);
                v___x_2353_ = lean_usize_land(v___x_2349_, v___x_2352_);
                v_bkt_2354_ = lean_array_uget_borrowed(v_buckets_2340_, v___x_2353_);
                v___x_2355_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(v_a_2337_, v_bkt_2354_);
                if v___x_2355_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2340_);
                    leanh::lean_inc(v_size_2339_);
                    v_isSharedCheck_2376_ = (!leanh::lean_is_exclusive(v_m_2336_)) as u8;
                    if v_isSharedCheck_2376_ == 0 {
                        v_unused_2377_ = leanh::lean_ctor_get(v_m_2336_, 1);
                        leanh::lean_dec(v_unused_2377_);
                        v_unused_2378_ = leanh::lean_ctor_get(v_m_2336_, 0);
                        leanh::lean_dec(v_unused_2378_);
                        v___x_2357_ = v_m_2336_;
                        v_isShared_2358_ = v_isSharedCheck_2376_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2336_);
                        v___x_2357_ = leanh::lean_box(0);
                        v_isShared_2358_ = v_isSharedCheck_2376_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2338_);
                    leanh::lean_dec_ref(v_a_2337_);
                    return v_m_2336_;
                }
            }
            1 => {
                v___x_2359_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2360_ = lean_nat_add(v_size_2339_, v___x_2359_);
                leanh::lean_dec(v_size_2339_);
                leanh::lean_inc(v_bkt_2354_);
                v___x_2361_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2361_, 0, v_a_2337_);
                leanh::lean_ctor_set(v___x_2361_, 1, v_b_2338_);
                leanh::lean_ctor_set(v___x_2361_, 2, v_bkt_2354_);
                v_buckets_x27_2362_ = lean_array_uset(v_buckets_2340_, v___x_2353_, v___x_2361_);
                v___x_2363_ = leanh::lean_unsigned_to_nat(4);
                v___x_2364_ = lean_nat_mul(v_size_x27_2360_, v___x_2363_);
                v___x_2365_ = leanh::lean_unsigned_to_nat(3);
                v___x_2366_ = lean_nat_div(v___x_2364_, v___x_2365_);
                leanh::lean_dec(v___x_2364_);
                v___x_2367_ = lean_array_get_size(v_buckets_x27_2362_);
                v___x_2368_ = lean_nat_dec_le(v___x_2366_, v___x_2367_);
                leanh::lean_dec(v___x_2366_);
                if v___x_2368_ == 0 {
                    v_val_2369_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4___redArg(v_buckets_x27_2362_);
                    if v_isShared_2358_ == 0 {
                        leanh::lean_ctor_set(v___x_2357_, 1, v_val_2369_);
                        leanh::lean_ctor_set(v___x_2357_, 0, v_size_x27_2360_);
                        v___x_2371_ = v___x_2357_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2372_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_size_x27_2360_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_val_2369_);
                        v___x_2371_ = v_reuseFailAlloc_2372_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2358_ == 0 {
                        leanh::lean_ctor_set(v___x_2357_, 1, v_buckets_x27_2362_);
                        leanh::lean_ctor_set(v___x_2357_, 0, v_size_x27_2360_);
                        v___x_2374_ = v___x_2357_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_size_x27_2360_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_buckets_x27_2362_);
                        v___x_2374_ = v_reuseFailAlloc_2375_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2371_;
            }
            3 => {
                return v___x_2374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_2379_: *mut leanh::LeanObject,
    mut v_sz_2380_: usize,
    mut v_i_2381_: usize,
    mut v_b_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2383_: u8 = 0;
    let mut v_a_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: usize = 0;
    let mut v___x_2388_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2383_ = lean_usize_dec_lt(v_i_2381_, v_sz_2380_);
                if v___x_2383_ == 0 {
                    return v_b_2382_;
                } else {
                    v_a_2384_ = lean_array_uget_borrowed(v_as_2379_, v_i_2381_);
                    v___x_2385_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_2384_);
                    v_r_2386_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(v_b_2382_, v_a_2384_, v___x_2385_);
                    v___x_2387_ = 1usize;
                    v___x_2388_ = lean_usize_add(v_i_2381_, v___x_2387_);
                    v_i_2381_ = v___x_2388_;
                    v_b_2382_ = v_r_2386_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_2390_: *mut leanh::LeanObject,
    mut v_sz_2391_: *mut leanh::LeanObject,
    mut v_i_2392_: *mut leanh::LeanObject,
    mut v_b_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2394_: usize = 0;
    let mut v_i_boxed_2395_: usize = 0;
    let mut v_res_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2394_ = leanh::lean_unbox_usize(v_sz_2391_);
    leanh::lean_dec(v_sz_2391_);
    v_i_boxed_2395_ = leanh::lean_unbox_usize(v_i_2392_);
    leanh::lean_dec(v_i_2392_);
    v_res_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0(v_as_2390_, v_sz_boxed_2394_, v_i_boxed_2395_, v_b_2393_);
    leanh::lean_dec_ref(v_as_2390_);
    return v_res_2396_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0(
    mut v_m_2397_: *mut leanh::LeanObject,
    mut v_l_2398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_2399_: usize = 0;
    let mut v___x_2400_: usize = 0;
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_2399_ = lean_array_size(v_l_2398_);
    v___x_2400_ = 0usize;
    v___x_2401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0_spec__0(v_l_2398_, v_sz_2399_, v___x_2400_, v_m_2397_);
    return v___x_2401_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0___boxed(
    mut v_m_2402_: *mut leanh::LeanObject,
    mut v_l_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0(v_m_2402_, v_l_2403_);
    leanh::lean_dec_ref(v_l_2403_);
    return v_res_2404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(
    mut v_as_2405_: *mut leanh::LeanObject,
    mut v_i_2406_: usize,
    mut v_stop_2407_: usize,
    mut v_b_2408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: usize = 0;
    let mut v___x_2413_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2409_ = lean_usize_dec_eq(v_i_2406_, v_stop_2407_);
                if v___x_2409_ == 0 {
                    v___x_2410_ = lean_array_uget_borrowed(v_as_2405_, v_i_2406_);
                    v___x_2411_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__0(v_b_2408_, v___x_2410_);
                    v___x_2412_ = 1usize;
                    v___x_2413_ = lean_usize_add(v_i_2406_, v___x_2412_);
                    v_i_2406_ = v___x_2413_;
                    v_b_2408_ = v___x_2411_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2408_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_2415_: *mut leanh::LeanObject,
    mut v_i_2416_: *mut leanh::LeanObject,
    mut v_stop_2417_: *mut leanh::LeanObject,
    mut v_b_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2419_: usize = 0;
    let mut v_stop_boxed_2420_: usize = 0;
    let mut v_res_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2419_ = leanh::lean_unbox_usize(v_i_2416_);
    leanh::lean_dec(v_i_2416_);
    v_stop_boxed_2420_ = leanh::lean_unbox_usize(v_stop_2417_);
    leanh::lean_dec(v_stop_2417_);
    v_res_2421_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(v_as_2415_, v_i_boxed_2419_, v_stop_boxed_2420_, v_b_2418_);
    leanh::lean_dec_ref(v_as_2415_);
    return v_res_2421_;
}
pub unsafe fn _init_l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2422_ = leanh::lean_box(0);
    v___x_2423_ = leanh::lean_unsigned_to_nat(16);
    v___x_2424_ = lean_mk_array(v___x_2423_, v___x_2422_);
    return v___x_2424_;
}
pub unsafe fn _init_l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2425_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__0_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_);
    v___x_2426_ = leanh::lean_unsigned_to_nat(0);
    v___x_2427_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2427_, 0, v___x_2426_);
    leanh::lean_ctor_set(v___x_2427_, 1, v___x_2425_);
    return v___x_2427_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(
    mut v_as_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    v___x_2429_ = leanh::lean_unsigned_to_nat(0);
    v___x_2430_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__once), _init_l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1___closed__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_);
    v___x_2431_ = lean_array_get_size(v_as_2428_);
    v___x_2432_ = lean_nat_dec_lt(v___x_2429_, v___x_2431_);
    if v___x_2432_ == 0 {
        return v___x_2430_;
    } else {
        let mut v___x_2433_: u8 = 0;
        v___x_2433_ = lean_nat_dec_le(v___x_2431_, v___x_2431_);
        if v___x_2433_ == 0 {
            if v___x_2432_ == 0 {
                return v___x_2430_;
            } else {
                let mut v___x_2434_: usize = 0;
                let mut v___x_2435_: usize = 0;
                let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2434_ = 0usize;
                v___x_2435_ = lean_usize_of_nat(v___x_2431_);
                v___x_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(v_as_2428_, v___x_2434_, v___x_2435_, v___x_2430_);
                return v___x_2436_;
            }
        } else {
            let mut v___x_2437_: usize = 0;
            let mut v___x_2438_: usize = 0;
            let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2437_ = 0usize;
            v___x_2438_ = lean_usize_of_nat(v___x_2431_);
            v___x_2439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__1(v_as_2428_, v___x_2437_, v___x_2438_, v___x_2430_);
            return v___x_2439_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed(
    mut v_as_2440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2441_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__1_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(v_as_2440_);
    leanh::lean_dec_ref(v_as_2440_);
    return v_res_2441_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___lam__2_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_(
    mut v___y_2442_: *mut leanh::LeanObject,
    mut v___y_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2444_ = leanh::lean_box(0);
    v___x_2445_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(v___y_2442_, v___y_2443_, v___x_2444_);
    return v___x_2445_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_;
    v___x_2467_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2466_);
    return v___x_2467_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2____boxed(
    mut v_a_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2469_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_();
    return v_res_2469_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2(
    mut v_00_u03b2_2470_: *mut leanh::LeanObject,
    mut v_m_2471_: *mut leanh::LeanObject,
    mut v_a_2472_: *mut leanh::LeanObject,
    mut v_b_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2___redArg(v_m_2471_, v_a_2472_, v_b_2473_);
    return v___x_2474_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3(
    mut v_00_u03b2_2475_: *mut leanh::LeanObject,
    mut v_a_2476_: *mut leanh::LeanObject,
    mut v_x_2477_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2478_: u8 = 0;
    v___x_2478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___redArg(v_a_2476_, v_x_2477_);
    return v___x_2478_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_00_u03b2_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
    mut v_x_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2482_: u8 = 0;
    let mut v_r_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__3(v_00_u03b2_2479_, v_a_2480_, v_x_2481_);
    leanh::lean_dec(v_x_2481_);
    leanh::lean_dec_ref(v_a_2480_);
    v_r_2483_ = leanh::lean_box((v_res_2482_) as usize);
    return v_r_2483_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4(
    mut v_00_u03b2_2484_: *mut leanh::LeanObject,
    mut v_data_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4___redArg(v_data_2485_);
    return v___x_2486_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5(
    mut v_00_u03b2_2487_: *mut leanh::LeanObject,
    mut v_i_2488_: *mut leanh::LeanObject,
    mut v_source_2489_: *mut leanh::LeanObject,
    mut v_target_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5___redArg(v_i_2488_, v_source_2489_, v_target_2490_);
    return v___x_2491_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6(
    mut v_00_u03b2_2492_: *mut leanh::LeanObject,
    mut v_x_2493_: *mut leanh::LeanObject,
    mut v_x_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2495_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2__spec__2_spec__4_spec__5_spec__6___redArg(v_x_2493_, v_x_2494_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Elab_Command_addAssertExistsEntry___redArg(
    mut v_isDecl_2496_: u8,
    mut v_declName_2497_: *mut leanh::LeanObject,
    mut v_mod_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_st_ref_take(v_a_2499_);
                v_env_2502_ = leanh::lean_ctor_get(v___x_2501_, 0);
                v_messages_2503_ = leanh::lean_ctor_get(v___x_2501_, 1);
                v_scopes_2504_ = leanh::lean_ctor_get(v___x_2501_, 2);
                v_usedQuotCtxts_2505_ = leanh::lean_ctor_get(v___x_2501_, 3);
                v_nextMacroScope_2506_ = leanh::lean_ctor_get(v___x_2501_, 4);
                v_maxRecDepth_2507_ = leanh::lean_ctor_get(v___x_2501_, 5);
                v_ngen_2508_ = leanh::lean_ctor_get(v___x_2501_, 6);
                v_auxDeclNGen_2509_ = leanh::lean_ctor_get(v___x_2501_, 7);
                v_infoState_2510_ = leanh::lean_ctor_get(v___x_2501_, 8);
                v_traceState_2511_ = leanh::lean_ctor_get(v___x_2501_, 9);
                v_snapshotTasks_2512_ = leanh::lean_ctor_get(v___x_2501_, 10);
                v_isSharedCheck_2528_ = (!leanh::lean_is_exclusive(v___x_2501_)) as u8;
                if v_isSharedCheck_2528_ == 0 {
                    v___x_2514_ = v___x_2501_;
                    v_isShared_2515_ = v_isSharedCheck_2528_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2512_);
                    leanh::lean_inc(v_traceState_2511_);
                    leanh::lean_inc(v_infoState_2510_);
                    leanh::lean_inc(v_auxDeclNGen_2509_);
                    leanh::lean_inc(v_ngen_2508_);
                    leanh::lean_inc(v_maxRecDepth_2507_);
                    leanh::lean_inc(v_nextMacroScope_2506_);
                    leanh::lean_inc(v_usedQuotCtxts_2505_);
                    leanh::lean_inc(v_scopes_2504_);
                    leanh::lean_inc(v_messages_2503_);
                    leanh::lean_inc(v_env_2502_);
                    leanh::lean_dec(v___x_2501_);
                    v___x_2514_ = leanh::lean_box(0);
                    v_isShared_2515_ = v_isSharedCheck_2528_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2516_ = l_Lean_Elab_Command_assertExistsExt;
                v_toEnvExtension_2517_ = leanh::lean_ctor_get(v___x_2516_, 0);
                v_asyncMode_2518_ = leanh::lean_ctor_get(v_toEnvExtension_2517_, 2);
                v___x_2519_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_2519_, 0, v_declName_2497_);
                leanh::lean_ctor_set(v___x_2519_, 1, v_mod_2498_);
                leanh::lean_ctor_set_uint8(
                    v___x_2519_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_isDecl_2496_,
                );
                v___x_2520_ = leanh::lean_box(0);
                v___x_2521_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2516_,
                    v_env_2502_,
                    v___x_2519_,
                    v_asyncMode_2518_,
                    v___x_2520_,
                );
                if v_isShared_2515_ == 0 {
                    leanh::lean_ctor_set(v___x_2514_, 0, v___x_2521_);
                    v___x_2523_ = v___x_2514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2527_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_messages_2503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_scopes_2504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 3, v_usedQuotCtxts_2505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_nextMacroScope_2506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 5, v_maxRecDepth_2507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 6, v_ngen_2508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 7, v_auxDeclNGen_2509_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 8, v_infoState_2510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 9, v_traceState_2511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2527_, 10, v_snapshotTasks_2512_);
                    v___x_2523_ = v_reuseFailAlloc_2527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2524_ = lean_st_ref_set(v_a_2499_, v___x_2523_);
                v___x_2525_ = leanh::lean_box(0);
                v___x_2526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2526_, 0, v___x_2525_);
                return v___x_2526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_addAssertExistsEntry___redArg___boxed(
    mut v_isDecl_2529_: *mut leanh::LeanObject,
    mut v_declName_2530_: *mut leanh::LeanObject,
    mut v_mod_2531_: *mut leanh::LeanObject,
    mut v_a_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isDecl_boxed_2534_: u8 = 0;
    let mut v_res_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isDecl_boxed_2534_ = (leanh::lean_unbox(v_isDecl_2529_) as u8);
    v_res_2535_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(
        v_isDecl_boxed_2534_,
        v_declName_2530_,
        v_mod_2531_,
        v_a_2532_,
    );
    leanh::lean_dec(v_a_2532_);
    return v_res_2535_;
}
pub unsafe fn l_Lean_Elab_Command_addAssertExistsEntry(
    mut v_isDecl_2536_: u8,
    mut v_declName_2537_: *mut leanh::LeanObject,
    mut v_mod_2538_: *mut leanh::LeanObject,
    mut v_a_2539_: *mut leanh::LeanObject,
    mut v_a_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(
        v_isDecl_2536_,
        v_declName_2537_,
        v_mod_2538_,
        v_a_2540_,
    );
    return v___x_2542_;
}
pub unsafe fn l_Lean_Elab_Command_addAssertExistsEntry___boxed(
    mut v_isDecl_2543_: *mut leanh::LeanObject,
    mut v_declName_2544_: *mut leanh::LeanObject,
    mut v_mod_2545_: *mut leanh::LeanObject,
    mut v_a_2546_: *mut leanh::LeanObject,
    mut v_a_2547_: *mut leanh::LeanObject,
    mut v_a_2548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isDecl_boxed_2549_: u8 = 0;
    let mut v_res_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isDecl_boxed_2549_ = (leanh::lean_unbox(v_isDecl_2543_) as u8);
    v_res_2550_ = l_Lean_Elab_Command_addAssertExistsEntry(
        v_isDecl_boxed_2549_,
        v_declName_2544_,
        v_mod_2545_,
        v_a_2546_,
        v_a_2547_,
    );
    leanh::lean_dec(v_a_2547_);
    leanh::lean_dec_ref(v_a_2546_);
    return v_res_2550_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(
    mut v___x_2551_: u8,
    mut v_d_2552_: *mut leanh::LeanObject,
    mut v_e_2553_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_isDecl_2554_: u8 = 0;
    let mut v_givenName_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDecl_2556_: u8 = 0;
    let mut v_givenName_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2559_: u8 = 0;
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: u8 = 0;
    let mut v___x_2563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isDecl_2554_ = leanh::lean_ctor_get_uint8(
                    v_e_2553_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_givenName_2555_ = leanh::lean_ctor_get(v_e_2553_, 0);
                leanh::lean_inc(v_givenName_2555_);
                leanh::lean_dec_ref(v_e_2553_);
                v_isDecl_2556_ = leanh::lean_ctor_get_uint8(
                    v_d_2552_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_givenName_2557_ = leanh::lean_ctor_get(v_d_2552_, 0);
                leanh::lean_inc(v_givenName_2557_);
                leanh::lean_dec_ref(v_d_2552_);
                v___x_2563_ = l_Bool_instDecidableLt(v_isDecl_2554_, v_isDecl_2556_);
                if v___x_2563_ == 0 {
                    if v_isDecl_2554_ == 0 {
                        if v_isDecl_2556_ == 0 {
                            v___y_2559_ = v___x_2551_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_givenName_2557_);
                            leanh::lean_dec(v_givenName_2555_);
                            return v_isDecl_2554_;
                        }
                    } else {
                        if v_isDecl_2556_ == 0 {
                            leanh::lean_dec(v_givenName_2557_);
                            leanh::lean_dec(v_givenName_2555_);
                            return v_isDecl_2556_;
                        } else {
                            v___y_2559_ = v_isDecl_2556_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_givenName_2557_);
                    leanh::lean_dec(v_givenName_2555_);
                    return v___x_2563_;
                }
            }
            1 => {
                v___x_2560_ = l_Lean_Name_toString(v_givenName_2557_, v___y_2559_);
                v___x_2561_ = l_Lean_Name_toString(v_givenName_2555_, v___y_2559_);
                v___x_2562_ = lean_string_dec_lt(v___x_2560_, v___x_2561_);
                leanh::lean_dec_ref(v___x_2561_);
                leanh::lean_dec_ref(v___x_2560_);
                return v___x_2562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0___boxed(
    mut v___x_2564_: *mut leanh::LeanObject,
    mut v_d_2565_: *mut leanh::LeanObject,
    mut v_e_2566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_619__boxed_2567_: u8 = 0;
    let mut v_res_2568_: u8 = 0;
    let mut v_r_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_619__boxed_2567_ = (leanh::lean_unbox(v___x_2564_) as u8);
    v_res_2568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(v___x_619__boxed_2567_, v_d_2565_, v_e_2566_);
    v_r_2569_ = leanh::lean_box((v_res_2568_) as usize);
    return v_r_2569_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0___redArg(
    mut v_hi_2570_: *mut leanh::LeanObject,
    mut v_pivot_2571_: *mut leanh::LeanObject,
    mut v_as_2572_: *mut leanh::LeanObject,
    mut v_i_2573_: *mut leanh::LeanObject,
    mut v_k_2574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2580_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDecl_2589_: u8 = 0;
    let mut v_givenName_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: u8 = 0;
    let mut v_givenName_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v_isDecl_2598_: u8 = 0;
    let mut v___x_2599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2586_ = lean_nat_dec_lt(v_k_2574_, v_hi_2570_);
                if v___x_2586_ == 0 {
                    leanh::lean_dec(v_k_2574_);
                    leanh::lean_dec_ref(v_pivot_2571_);
                    v___x_2587_ = lean_array_fswap(v_as_2572_, v_i_2573_, v_hi_2570_);
                    v___x_2588_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2588_, 0, v_i_2573_);
                    leanh::lean_ctor_set(v___x_2588_, 1, v___x_2587_);
                    return v___x_2588_;
                } else {
                    v_isDecl_2589_ = leanh::lean_ctor_get_uint8(
                        v_pivot_2571_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_givenName_2590_ = leanh::lean_ctor_get(v_pivot_2571_, 0);
                    v___x_2591_ = lean_array_fget_borrowed(v_as_2572_, v_k_2574_);
                    v_isDecl_2598_ = leanh::lean_ctor_get_uint8(
                        v___x_2591_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_2599_ = l_Bool_instDecidableLt(v_isDecl_2589_, v_isDecl_2598_);
                    if v___x_2599_ == 0 {
                        if v_isDecl_2589_ == 0 {
                            if v_isDecl_2598_ == 0 {
                                v___y_2593_ = v___x_2586_;
                                state = 3;
                                continue;
                            } else {
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_2593_ = v_isDecl_2598_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_2580_ = v___x_2599_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2576_ = leanh::lean_unsigned_to_nat(1);
                v___x_2577_ = lean_nat_add(v_k_2574_, v___x_2576_);
                leanh::lean_dec(v_k_2574_);
                v_k_2574_ = v___x_2577_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2580_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2581_ = lean_array_fswap(v_as_2572_, v_i_2573_, v_k_2574_);
                    v___x_2582_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2583_ = lean_nat_add(v_i_2573_, v___x_2582_);
                    leanh::lean_dec(v_i_2573_);
                    v___x_2584_ = lean_nat_add(v_k_2574_, v___x_2582_);
                    leanh::lean_dec(v_k_2574_);
                    v_as_2572_ = v___x_2581_;
                    v_i_2573_ = v___x_2583_;
                    v_k_2574_ = v___x_2584_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                if v___y_2593_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_givenName_2594_ = leanh::lean_ctor_get(v___x_2591_, 0);
                    leanh::lean_inc(v_givenName_2594_);
                    v___x_2595_ = l_Lean_Name_toString(v_givenName_2594_, v___y_2593_);
                    leanh::lean_inc(v_givenName_2590_);
                    v___x_2596_ = l_Lean_Name_toString(v_givenName_2590_, v___y_2593_);
                    v___x_2597_ = lean_string_dec_lt(v___x_2595_, v___x_2596_);
                    leanh::lean_dec_ref(v___x_2596_);
                    leanh::lean_dec_ref(v___x_2595_);
                    v___y_2580_ = v___x_2597_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0___redArg___boxed(
    mut v_hi_2600_: *mut leanh::LeanObject,
    mut v_pivot_2601_: *mut leanh::LeanObject,
    mut v_as_2602_: *mut leanh::LeanObject,
    mut v_i_2603_: *mut leanh::LeanObject,
    mut v_k_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0___redArg(v_hi_2600_, v_pivot_2601_, v_as_2602_, v_i_2603_, v_k_2604_);
    leanh::lean_dec(v_hi_2600_);
    return v_res_2605_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(
    mut v_n_2606_: *mut leanh::LeanObject,
    mut v_as_2607_: *mut leanh::LeanObject,
    mut v_lo_2608_: *mut leanh::LeanObject,
    mut v_hi_2609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: u8 = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2621_ = lean_nat_dec_lt(v_lo_2608_, v_hi_2609_);
                if v___x_2621_ == 0 {
                    leanh::lean_dec(v_lo_2608_);
                    return v_as_2607_;
                } else {
                    v___x_2622_ = lean_nat_add(v_lo_2608_, v_hi_2609_);
                    v___x_2623_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2624_ = lean_nat_shiftr(v___x_2622_, v___x_2623_);
                    leanh::lean_dec(v___x_2622_);
                    v___x_2637_ = lean_array_fget_borrowed(v_as_2607_, v_mid_2624_);
                    v___x_2638_ = lean_array_fget_borrowed(v_as_2607_, v_lo_2608_);
                    leanh::lean_inc(v___x_2638_);
                    leanh::lean_inc(v___x_2637_);
                    v___x_2639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(v___x_2621_, v___x_2637_, v___x_2638_);
                    if v___x_2639_ == 0 {
                        v___y_2632_ = v_as_2607_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2640_ = lean_array_fswap(v_as_2607_, v_lo_2608_, v_mid_2624_);
                        v___y_2632_ = v___x_2640_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2612_ = lean_array_fget(v___y_2611_, v_hi_2609_);
                leanh::lean_inc_n(v_lo_2608_, 2);
                v___x_2613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0___redArg(v_hi_2609_, v_pivot_2612_, v___y_2611_, v_lo_2608_, v_lo_2608_);
                v_fst_2614_ = leanh::lean_ctor_get(v___x_2613_, 0);
                leanh::lean_inc(v_fst_2614_);
                v_snd_2615_ = leanh::lean_ctor_get(v___x_2613_, 1);
                leanh::lean_inc(v_snd_2615_);
                leanh::lean_dec_ref(v___x_2613_);
                v___x_2616_ = lean_nat_dec_le(v_hi_2609_, v_fst_2614_);
                if v___x_2616_ == 0 {
                    v___x_2617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v_n_2606_, v_snd_2615_, v_lo_2608_, v_fst_2614_);
                    v___x_2618_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2619_ = lean_nat_add(v_fst_2614_, v___x_2618_);
                    leanh::lean_dec(v_fst_2614_);
                    v_as_2607_ = v___x_2617_;
                    v_lo_2608_ = v___x_2619_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2614_);
                    leanh::lean_dec(v_lo_2608_);
                    return v_snd_2615_;
                }
            }
            2 => {
                v___x_2627_ = lean_array_fget_borrowed(v___y_2626_, v_mid_2624_);
                v___x_2628_ = lean_array_fget_borrowed(v___y_2626_, v_hi_2609_);
                leanh::lean_inc(v___x_2628_);
                leanh::lean_inc(v___x_2627_);
                v___x_2629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(v___x_2621_, v___x_2627_, v___x_2628_);
                if v___x_2629_ == 0 {
                    leanh::lean_dec(v_mid_2624_);
                    v___y_2611_ = v___y_2626_;
                    state = 1;
                    continue;
                } else {
                    v___x_2630_ = lean_array_fswap(v___y_2626_, v_mid_2624_, v_hi_2609_);
                    leanh::lean_dec(v_mid_2624_);
                    v___y_2611_ = v___x_2630_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2633_ = lean_array_fget_borrowed(v___y_2632_, v_hi_2609_);
                v___x_2634_ = lean_array_fget_borrowed(v___y_2632_, v_lo_2608_);
                leanh::lean_inc(v___x_2634_);
                leanh::lean_inc(v___x_2633_);
                v___x_2635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___lam__0(v___x_2621_, v___x_2633_, v___x_2634_);
                if v___x_2635_ == 0 {
                    v___y_2626_ = v___y_2632_;
                    state = 2;
                    continue;
                } else {
                    v___x_2636_ = lean_array_fswap(v___y_2632_, v_lo_2608_, v_hi_2609_);
                    v___y_2626_ = v___x_2636_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg___boxed(
    mut v_n_2641_: *mut leanh::LeanObject,
    mut v_as_2642_: *mut leanh::LeanObject,
    mut v_lo_2643_: *mut leanh::LeanObject,
    mut v_hi_2644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v_n_2641_, v_as_2642_, v_lo_2643_, v_hi_2644_);
    leanh::lean_dec(v_hi_2644_);
    leanh::lean_dec(v_n_2641_);
    return v_res_2645_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Command_getSortedAssertExists_spec__1(
    mut v_x_2646_: *mut leanh::LeanObject,
    mut v_x_2647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2647_) == 0 {
                    return v_x_2646_;
                } else {
                    v_key_2648_ = leanh::lean_ctor_get(v_x_2647_, 0);
                    leanh::lean_inc(v_key_2648_);
                    v_tail_2649_ = leanh::lean_ctor_get(v_x_2647_, 2);
                    leanh::lean_inc(v_tail_2649_);
                    leanh::lean_dec_ref_known(v_x_2647_, 3);
                    v___x_2650_ = lean_array_push(v_x_2646_, v_key_2648_);
                    v_x_2646_ = v___x_2650_;
                    v_x_2647_ = v_tail_2649_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(
    mut v_as_2652_: *mut leanh::LeanObject,
    mut v_i_2653_: usize,
    mut v_stop_2654_: usize,
    mut v_b_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2656_: u8 = 0;
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: usize = 0;
    let mut v___x_2660_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2656_ = lean_usize_dec_eq(v_i_2653_, v_stop_2654_);
                if v___x_2656_ == 0 {
                    v___x_2657_ = lean_array_uget_borrowed(v_as_2652_, v_i_2653_);
                    leanh::lean_inc(v___x_2657_);
                    v___x_2658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Command_getSortedAssertExists_spec__1(v_b_2655_, v___x_2657_);
                    v___x_2659_ = 1usize;
                    v___x_2660_ = lean_usize_add(v_i_2653_, v___x_2659_);
                    v_i_2653_ = v___x_2660_;
                    v_b_2655_ = v___x_2658_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2655_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2___boxed(
    mut v_as_2662_: *mut leanh::LeanObject,
    mut v_i_2663_: *mut leanh::LeanObject,
    mut v_stop_2664_: *mut leanh::LeanObject,
    mut v_b_2665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2666_: usize = 0;
    let mut v_stop_boxed_2667_: usize = 0;
    let mut v_res_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2666_ = leanh::lean_unbox_usize(v_i_2663_);
    leanh::lean_dec(v_i_2663_);
    v_stop_boxed_2667_ = leanh::lean_unbox_usize(v_stop_2664_);
    leanh::lean_dec(v_stop_2664_);
    v_res_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(v_as_2662_, v_i_boxed_2666_, v_stop_boxed_2667_, v_b_2665_);
    leanh::lean_dec_ref(v_as_2662_);
    return v_res_2668_;
}
pub unsafe fn _init_l_Lean_Elab_Command_getSortedAssertExists___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = l_Lean_Elab_Command_instHashableAssertExists___closed__0;
    v___x_2670_ = l_Lean_Elab_Command_instBEqAssertExists___closed__0;
    v___x_2671_ = l_Std_HashSet_instInhabited(leanh::lean_box(0), v___x_2670_, v___x_2669_);
    return v___x_2671_;
}
pub unsafe fn l_Lean_Elab_Command_getSortedAssertExists(
    mut v_env_2672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: u8 = 0;
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: u8 = 0;
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: u8 = 0;
    let mut v___x_2702_: usize = 0;
    let mut v___x_2703_: usize = 0;
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: usize = 0;
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2689_ = l_Lean_Elab_Command_assertExistsExt;
                v_toEnvExtension_2690_ = leanh::lean_ctor_get(v___x_2689_, 0);
                v_asyncMode_2691_ = leanh::lean_ctor_get(v_toEnvExtension_2690_, 2);
                v___x_2692_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_getSortedAssertExists___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_getSortedAssertExists___closed__0_once
                    ),
                    _init_l_Lean_Elab_Command_getSortedAssertExists___closed__0,
                );
                v___x_2693_ = leanh::lean_box(0);
                v___x_2694_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_2692_,
                    v___x_2689_,
                    v_env_2672_,
                    v_asyncMode_2691_,
                    v___x_2693_,
                );
                v_size_2695_ = leanh::lean_ctor_get(v___x_2694_, 0);
                leanh::lean_inc(v_size_2695_);
                v_buckets_2696_ = leanh::lean_ctor_get(v___x_2694_, 1);
                leanh::lean_inc_ref(v_buckets_2696_);
                leanh::lean_dec(v___x_2694_);
                v___x_2697_ = lean_mk_empty_array_with_capacity(v_size_2695_);
                leanh::lean_dec(v_size_2695_);
                v___x_2698_ = leanh::lean_unsigned_to_nat(0);
                v___x_2699_ = lean_array_get_size(v_buckets_2696_);
                v___x_2700_ = lean_nat_dec_lt(v___x_2698_, v___x_2699_);
                if v___x_2700_ == 0 {
                    leanh::lean_dec_ref(v_buckets_2696_);
                    v___y_2682_ = v___x_2697_;
                    state = 2;
                    continue;
                } else {
                    v___x_2701_ = lean_nat_dec_le(v___x_2699_, v___x_2699_);
                    if v___x_2701_ == 0 {
                        if v___x_2700_ == 0 {
                            leanh::lean_dec_ref(v_buckets_2696_);
                            v___y_2682_ = v___x_2697_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2702_ = 0usize;
                            v___x_2703_ = lean_usize_of_nat(v___x_2699_);
                            v___x_2704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(v_buckets_2696_, v___x_2702_, v___x_2703_, v___x_2697_);
                            leanh::lean_dec_ref(v_buckets_2696_);
                            v___y_2682_ = v___x_2704_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2705_ = 0usize;
                        v___x_2706_ = lean_usize_of_nat(v___x_2699_);
                        v___x_2707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_getSortedAssertExists_spec__2(v_buckets_2696_, v___x_2705_, v___x_2706_, v___x_2697_);
                        leanh::lean_dec_ref(v_buckets_2696_);
                        v___y_2682_ = v___x_2707_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2678_ = lean_nat_dec_le(v___y_2677_, v___y_2675_);
                if v___x_2678_ == 0 {
                    leanh::lean_dec(v___y_2675_);
                    leanh::lean_inc(v___y_2677_);
                    v___x_2679_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v___y_2674_, v___y_2676_, v___y_2677_, v___y_2677_);
                    leanh::lean_dec(v___y_2677_);
                    leanh::lean_dec(v___y_2674_);
                    return v___x_2679_;
                } else {
                    v___x_2680_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v___y_2674_, v___y_2676_, v___y_2677_, v___y_2675_);
                    leanh::lean_dec(v___y_2675_);
                    leanh::lean_dec(v___y_2674_);
                    return v___x_2680_;
                }
            }
            2 => {
                v___x_2683_ = lean_array_get_size(v___y_2682_);
                v___x_2684_ = leanh::lean_unsigned_to_nat(0);
                v___x_2685_ = lean_nat_dec_eq(v___x_2683_, v___x_2684_);
                if v___x_2685_ == 0 {
                    v___x_2686_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2687_ = lean_nat_sub(v___x_2683_, v___x_2686_);
                    v___x_2688_ = lean_nat_dec_le(v___x_2684_, v___x_2687_);
                    if v___x_2688_ == 0 {
                        leanh::lean_inc(v___x_2687_);
                        v___y_2674_ = v___x_2683_;
                        v___y_2675_ = v___x_2687_;
                        v___y_2676_ = v___y_2682_;
                        v___y_2677_ = v___x_2687_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2674_ = v___x_2683_;
                        v___y_2675_ = v___x_2687_;
                        v___y_2676_ = v___y_2682_;
                        v___y_2677_ = v___x_2684_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_2682_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0(
    mut v_n_2708_: *mut leanh::LeanObject,
    mut v_as_2709_: *mut leanh::LeanObject,
    mut v_lo_2710_: *mut leanh::LeanObject,
    mut v_hi_2711_: *mut leanh::LeanObject,
    mut v_w_2712_: *mut leanh::LeanObject,
    mut v_hlo_2713_: *mut leanh::LeanObject,
    mut v_hhi_2714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___redArg(v_n_2708_, v_as_2709_, v_lo_2710_, v_hi_2711_);
    return v___x_2715_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0___boxed(
    mut v_n_2716_: *mut leanh::LeanObject,
    mut v_as_2717_: *mut leanh::LeanObject,
    mut v_lo_2718_: *mut leanh::LeanObject,
    mut v_hi_2719_: *mut leanh::LeanObject,
    mut v_w_2720_: *mut leanh::LeanObject,
    mut v_hlo_2721_: *mut leanh::LeanObject,
    mut v_hhi_2722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0(v_n_2716_, v_as_2717_, v_lo_2718_, v_hi_2719_, v_w_2720_, v_hlo_2721_, v_hhi_2722_);
    leanh::lean_dec(v_hi_2719_);
    leanh::lean_dec(v_n_2716_);
    return v_res_2723_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0(
    mut v_n_2724_: *mut leanh::LeanObject,
    mut v_lo_2725_: *mut leanh::LeanObject,
    mut v_hi_2726_: *mut leanh::LeanObject,
    mut v_hhi_2727_: *mut leanh::LeanObject,
    mut v_pivot_2728_: *mut leanh::LeanObject,
    mut v_as_2729_: *mut leanh::LeanObject,
    mut v_i_2730_: *mut leanh::LeanObject,
    mut v_k_2731_: *mut leanh::LeanObject,
    mut v_ilo_2732_: *mut leanh::LeanObject,
    mut v_ik_2733_: *mut leanh::LeanObject,
    mut v_w_2734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0___redArg(v_hi_2726_, v_pivot_2728_, v_as_2729_, v_i_2730_, v_k_2731_);
    return v___x_2735_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0___boxed(
    mut v_n_2736_: *mut leanh::LeanObject,
    mut v_lo_2737_: *mut leanh::LeanObject,
    mut v_hi_2738_: *mut leanh::LeanObject,
    mut v_hhi_2739_: *mut leanh::LeanObject,
    mut v_pivot_2740_: *mut leanh::LeanObject,
    mut v_as_2741_: *mut leanh::LeanObject,
    mut v_i_2742_: *mut leanh::LeanObject,
    mut v_k_2743_: *mut leanh::LeanObject,
    mut v_ilo_2744_: *mut leanh::LeanObject,
    mut v_ik_2745_: *mut leanh::LeanObject,
    mut v_w_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Command_getSortedAssertExists_spec__0_spec__0(v_n_2736_, v_lo_2737_, v_hi_2738_, v_hhi_2739_, v_pivot_2740_, v_as_2741_, v_i_2742_, v_k_2743_, v_ilo_2744_, v_ik_2745_, v_w_2746_);
    leanh::lean_dec(v_hi_2738_);
    leanh::lean_dec(v_lo_2737_);
    leanh::lean_dec(v_n_2736_);
    return v_res_2747_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__0;
    v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
    return v___x_2750_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__2;
    v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
    return v___x_2753_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(
    mut v_as_2754_: *mut leanh::LeanObject,
    mut v_i_2755_: usize,
    mut v_stop_2756_: usize,
    mut v_b_2757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2758_: u8 = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: usize = 0;
    let mut v___x_2767_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2758_ = lean_usize_dec_eq(v_i_2755_, v_stop_2756_);
                if v___x_2758_ == 0 {
                    v___x_2759_ = lean_array_uget_borrowed(v_as_2754_, v_i_2755_);
                    v___x_2760_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__1);
                    leanh::lean_inc(v___x_2759_);
                    v___x_2761_ = l_Lean_MessageData_ofName(v___x_2759_);
                    v___x_2762_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2762_, 0, v___x_2760_);
                    leanh::lean_ctor_set(v___x_2762_, 1, v___x_2761_);
                    v___x_2763_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3);
                    v___x_2764_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2764_, 0, v___x_2762_);
                    leanh::lean_ctor_set(v___x_2764_, 1, v___x_2763_);
                    v___x_2765_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2765_, 0, v_b_2757_);
                    leanh::lean_ctor_set(v___x_2765_, 1, v___x_2764_);
                    v___x_2766_ = 1usize;
                    v___x_2767_ = lean_usize_add(v_i_2755_, v___x_2766_);
                    v_i_2755_ = v___x_2767_;
                    v_b_2757_ = v___x_2765_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2757_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___boxed(
    mut v_as_2769_: *mut leanh::LeanObject,
    mut v_i_2770_: *mut leanh::LeanObject,
    mut v_stop_2771_: *mut leanh::LeanObject,
    mut v_b_2772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2773_: usize = 0;
    let mut v_stop_boxed_2774_: usize = 0;
    let mut v_res_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2773_ = leanh::lean_unbox_usize(v_i_2770_);
    leanh::lean_dec(v_i_2770_);
    v_stop_boxed_2774_ = leanh::lean_unbox_usize(v_stop_2771_);
    leanh::lean_dec(v_stop_2771_);
    v_res_2775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(v_as_2769_, v_i_boxed_2773_, v_stop_boxed_2774_, v_b_2772_);
    leanh::lean_dec_ref(v_as_2769_);
    return v_res_2775_;
}
pub unsafe fn _init_l_Lean_Elab_Command_importPathMessage___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2777_ = l_Lean_Elab_Command_importPathMessage___closed__0;
    v___x_2778_ = l_Lean_stringToMessageData(v___x_2777_);
    return v___x_2778_;
}
pub unsafe fn l_Lean_Elab_Command_importPathMessage(
    mut v_env_2779_: *mut leanh::LeanObject,
    mut v_idx_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modNames_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: u8 = 0;
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2797_: usize = 0;
    let mut v___x_2798_: usize = 0;
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: usize = 0;
    let mut v___x_2801_: usize = 0;
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2785_ = leanh::lean_box(0);
                v___x_2786_ = l_Lean_Environment_header(v_env_2779_);
                v_modNames_2787_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2786_);
                v___x_2788_ = lean_array_get(v___x_2785_, v_modNames_2787_, v_idx_2780_);
                leanh::lean_dec_ref(v_modNames_2787_);
                leanh::lean_inc(v___x_2788_);
                v___x_2789_ = l_Lean_MessageData_ofName(v___x_2788_);
                v___x_2790_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0___closed__3);
                v___x_2791_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2791_, 0, v___x_2789_);
                leanh::lean_ctor_set(v___x_2791_, 1, v___x_2790_);
                v___x_2792_ = l_Lean_Environment_importPath(v_env_2779_, v___x_2788_);
                v___x_2793_ = leanh::lean_unsigned_to_nat(0);
                v___x_2794_ = lean_array_get_size(v___x_2792_);
                v___x_2795_ = lean_nat_dec_lt(v___x_2793_, v___x_2794_);
                if v___x_2795_ == 0 {
                    leanh::lean_dec_ref(v___x_2792_);
                    v___y_2782_ = v___x_2791_;
                    state = 1;
                    continue;
                } else {
                    v___x_2796_ = lean_nat_dec_le(v___x_2794_, v___x_2794_);
                    if v___x_2796_ == 0 {
                        if v___x_2795_ == 0 {
                            leanh::lean_dec_ref(v___x_2792_);
                            v___y_2782_ = v___x_2791_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2797_ = 0usize;
                            v___x_2798_ = lean_usize_of_nat(v___x_2794_);
                            v___x_2799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(v___x_2792_, v___x_2797_, v___x_2798_, v___x_2791_);
                            leanh::lean_dec_ref(v___x_2792_);
                            v___y_2782_ = v___x_2799_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2800_ = 0usize;
                        v___x_2801_ = lean_usize_of_nat(v___x_2794_);
                        v___x_2802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_importPathMessage_spec__0(v___x_2792_, v___x_2800_, v___x_2801_, v___x_2791_);
                        leanh::lean_dec_ref(v___x_2792_);
                        v___y_2782_ = v___x_2802_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2783_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_importPathMessage___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_importPathMessage___closed__1_once),
                    _init_l_Lean_Elab_Command_importPathMessage___closed__1,
                );
                v___x_2784_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2784_, 0, v___y_2782_);
                leanh::lean_ctor_set(v___x_2784_, 1, v___x_2783_);
                return v___x_2784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_importPathMessage___boxed(
    mut v_env_2803_: *mut leanh::LeanObject,
    mut v_idx_2804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2805_ = l_Lean_Elab_Command_importPathMessage(v_env_2803_, v_idx_2804_);
    leanh::lean_dec(v_idx_2804_);
    leanh::lean_dec_ref(v_env_2803_);
    return v_res_2805_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0(
    mut v___y_2807_: u8,
    mut v_suppressElabErrors_2808_: u8,
    mut v_x_2809_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2809_) == 1 {
        let mut v_pre_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2810_ = leanh::lean_ctor_get(v_x_2809_, 0);
        if leanh::lean_obj_tag(v_pre_2810_) == 0 {
            let mut v_str_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2813_: u8 = 0;
            v_str_2811_ = leanh::lean_ctor_get(v_x_2809_, 1);
            v___x_2812_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___closed__0;
            v___x_2813_ = lean_string_dec_eq(v_str_2811_, v___x_2812_);
            if v___x_2813_ == 0 {
                return v___y_2807_;
            } else {
                return v_suppressElabErrors_2808_;
            }
        } else {
            return v___y_2807_;
        }
    } else {
        return v___y_2807_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___boxed(
    mut v___y_2814_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2815_: *mut leanh::LeanObject,
    mut v_x_2816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6041__boxed_2817_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2818_: u8 = 0;
    let mut v_res_2819_: u8 = 0;
    let mut v_r_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_6041__boxed_2817_ = (leanh::lean_unbox(v___y_2814_) as u8);
    v_suppressElabErrors_boxed_2818_ = (leanh::lean_unbox(v_suppressElabErrors_2815_) as u8);
    v_res_2819_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0(v___y_6041__boxed_2817_, v_suppressElabErrors_boxed_2818_, v_x_2816_);
    leanh::lean_dec(v_x_2816_);
    v_r_2820_ = leanh::lean_box((v_res_2819_) as usize);
    return v_r_2820_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(
    mut v_opts_2821_: *mut leanh::LeanObject,
    mut v_opt_2822_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2823_ = leanh::lean_ctor_get(v_opt_2822_, 0);
    v_defValue_2824_ = leanh::lean_ctor_get(v_opt_2822_, 1);
    v_map_2825_ = leanh::lean_ctor_get(v_opts_2821_, 0);
    v___x_2826_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2825_,
            v_name_2823_,
        );
    if leanh::lean_obj_tag(v___x_2826_) == 0 {
        let mut v___x_2827_: u8 = 0;
        v___x_2827_ = (leanh::lean_unbox(v_defValue_2824_) as u8);
        return v___x_2827_;
    } else {
        let mut v_val_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2828_ = leanh::lean_ctor_get(v___x_2826_, 0);
        leanh::lean_inc(v_val_2828_);
        leanh::lean_dec_ref_known(v___x_2826_, 1);
        if leanh::lean_obj_tag(v_val_2828_) == 1 {
            let mut v_v_2829_: u8 = 0;
            v_v_2829_ = leanh::lean_ctor_get_uint8(v_val_2828_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2828_, 0);
            return v_v_2829_;
        } else {
            let mut v___x_2830_: u8 = 0;
            leanh::lean_dec(v_val_2828_);
            v___x_2830_ = (leanh::lean_unbox(v_defValue_2824_) as u8);
            return v___x_2830_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6___boxed(
    mut v_opts_2831_: *mut leanh::LeanObject,
    mut v_opt_2832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2833_: u8 = 0;
    let mut v_r_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2833_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(v_opts_2831_, v_opt_2832_);
    leanh::lean_dec_ref(v_opt_2832_);
    leanh::lean_dec_ref(v_opts_2831_);
    v_r_2834_ = leanh::lean_box((v_res_2833_) as usize);
    return v_r_2834_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2835_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2836_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__0);
    v___x_2837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2837_, 0, v___x_2836_);
    return v___x_2837_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2838_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1);
    v___x_2839_ = leanh::lean_unsigned_to_nat(0);
    v___x_2840_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2840_, 0, v___x_2839_);
    leanh::lean_ctor_set(v___x_2840_, 1, v___x_2839_);
    leanh::lean_ctor_set(v___x_2840_, 2, v___x_2839_);
    leanh::lean_ctor_set(v___x_2840_, 3, v___x_2839_);
    leanh::lean_ctor_set(v___x_2840_, 4, v___x_2838_);
    leanh::lean_ctor_set(v___x_2840_, 5, v___x_2838_);
    leanh::lean_ctor_set(v___x_2840_, 6, v___x_2838_);
    leanh::lean_ctor_set(v___x_2840_, 7, v___x_2838_);
    leanh::lean_ctor_set(v___x_2840_, 8, v___x_2838_);
    leanh::lean_ctor_set(v___x_2840_, 9, v___x_2838_);
    return v___x_2840_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2841_ = leanh::lean_unsigned_to_nat(32);
    v___x_2842_ = lean_mk_empty_array_with_capacity(v___x_2841_);
    v___x_2843_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2843_, 0, v___x_2842_);
    return v___x_2843_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2844_: usize = 0;
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = 5usize;
    v___x_2845_ = leanh::lean_unsigned_to_nat(0);
    v___x_2846_ = leanh::lean_unsigned_to_nat(32);
    v___x_2847_ = lean_mk_empty_array_with_capacity(v___x_2846_);
    v___x_2848_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__3);
    v___x_2849_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2849_, 0, v___x_2848_);
    leanh::lean_ctor_set(v___x_2849_, 1, v___x_2847_);
    leanh::lean_ctor_set(v___x_2849_, 2, v___x_2845_);
    leanh::lean_ctor_set(v___x_2849_, 3, v___x_2845_);
    leanh::lean_ctor_set_usize(v___x_2849_, 4, v___x_2844_);
    return v___x_2849_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2850_ = leanh::lean_box(1);
    v___x_2851_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__4);
    v___x_2852_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__1);
    v___x_2853_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2853_, 0, v___x_2852_);
    leanh::lean_ctor_set(v___x_2853_, 1, v___x_2851_);
    leanh::lean_ctor_set(v___x_2853_, 2, v___x_2850_);
    return v___x_2853_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(
    mut v_msgData_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2857_ = lean_st_ref_get(v___y_2855_);
    v_env_2858_ = leanh::lean_ctor_get(v___x_2857_, 0);
    leanh::lean_inc_ref(v_env_2858_);
    leanh::lean_dec(v___x_2857_);
    v___x_2859_ = lean_st_ref_get(v___y_2855_);
    v_scopes_2860_ = leanh::lean_ctor_get(v___x_2859_, 2);
    leanh::lean_inc(v_scopes_2860_);
    leanh::lean_dec(v___x_2859_);
    v___x_2861_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2862_ = l_List_head_x21___redArg(v___x_2861_, v_scopes_2860_);
    leanh::lean_dec(v_scopes_2860_);
    v_opts_2863_ = leanh::lean_ctor_get(v___x_2862_, 1);
    leanh::lean_inc_ref(v_opts_2863_);
    leanh::lean_dec(v___x_2862_);
    v___x_2864_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2);
    v___x_2865_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5);
    v___x_2866_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2866_, 0, v_env_2858_);
    leanh::lean_ctor_set(v___x_2866_, 1, v___x_2864_);
    leanh::lean_ctor_set(v___x_2866_, 2, v___x_2865_);
    leanh::lean_ctor_set(v___x_2866_, 3, v_opts_2863_);
    v___x_2867_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2867_, 0, v___x_2866_);
    leanh::lean_ctor_set(v___x_2867_, 1, v_msgData_2854_);
    v___x_2868_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2868_, 0, v___x_2867_);
    return v___x_2868_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_msgData_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2872_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v_msgData_2869_, v___y_2870_);
    leanh::lean_dec(v___y_2870_);
    return v_res_2872_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(
    mut v_ref_2874_: *mut leanh::LeanObject,
    mut v_msgData_2875_: *mut leanh::LeanObject,
    mut v_severity_2876_: u8,
    mut v_isSilent_2877_: u8,
    mut v___y_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: u8 = 0;
    let mut v___y_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: u8 = 0;
    let mut v___y_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2913_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_isSharedCheck_2927_: u8 = 0;
    let mut v_a_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_a_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v___y_2945_: u8 = 0;
    let mut v___y_2946_: u8 = 0;
    let mut v___y_2947_: u8 = 0;
    let mut v___y_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2952_: u8 = 0;
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: u8 = 0;
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2971_: u8 = 0;
    let mut v___y_2973_: u8 = 0;
    let mut v___y_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: u8 = 0;
    let mut v___y_2976_: u8 = 0;
    let mut v___y_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2981_: u8 = 0;
    let mut v___y_2982_: u8 = 0;
    let mut v___y_2983_: u8 = 0;
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut v___x_2998_: u8 = 0;
    let mut v___y_3000_: u8 = 0;
    let mut v___y_3001_: u8 = 0;
    let mut v___y_3002_: u8 = 0;
    let mut v___y_3004_: u8 = 0;
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: u8 = 0;
    let mut v___x_3011_: u8 = 0;
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: u8 = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2998_ = 2;
                v___x_3016_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2876_, v___x_2998_);
                if v___x_3016_ == 0 {
                    v___y_3004_ = v___x_3016_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2875_);
                    v___x_3017_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2875_);
                    v___y_3004_ = v___x_3017_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_2890_ = l_Lean_Elab_Command_getScope___redArg(v___y_2889_);
                if leanh::lean_obj_tag(v___x_2890_) == 0 {
                    v_a_2891_ = leanh::lean_ctor_get(v___x_2890_, 0);
                    leanh::lean_inc(v_a_2891_);
                    leanh::lean_dec_ref_known(v___x_2890_, 1);
                    v___x_2892_ = l_Lean_Elab_Command_getScope___redArg(v___y_2889_);
                    if leanh::lean_obj_tag(v___x_2892_) == 0 {
                        v_a_2893_ = leanh::lean_ctor_get(v___x_2892_, 0);
                        v_isSharedCheck_2927_ =
                            (!leanh::lean_is_exclusive(v___x_2892_)) as u8;
                        if v_isSharedCheck_2927_ == 0 {
                            v___x_2895_ = v___x_2892_;
                            v_isShared_2896_ = v_isSharedCheck_2927_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2893_);
                            leanh::lean_dec(v___x_2892_);
                            v___x_2895_ = leanh::lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_2927_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2891_);
                        leanh::lean_dec_ref(v___y_2887_);
                        leanh::lean_dec_ref(v___y_2885_);
                        leanh::lean_dec(v___y_2883_);
                        v_a_2928_ = leanh::lean_ctor_get(v___x_2892_, 0);
                        v_isSharedCheck_2935_ =
                            (!leanh::lean_is_exclusive(v___x_2892_)) as u8;
                        if v_isSharedCheck_2935_ == 0 {
                            v___x_2930_ = v___x_2892_;
                            v_isShared_2931_ = v_isSharedCheck_2935_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2928_);
                            leanh::lean_dec(v___x_2892_);
                            v___x_2930_ = leanh::lean_box(0);
                            v_isShared_2931_ = v_isSharedCheck_2935_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2887_);
                    leanh::lean_dec_ref(v___y_2885_);
                    leanh::lean_dec(v___y_2883_);
                    v_a_2936_ = leanh::lean_ctor_get(v___x_2890_, 0);
                    v_isSharedCheck_2943_ = (!leanh::lean_is_exclusive(v___x_2890_)) as u8;
                    if v_isSharedCheck_2943_ == 0 {
                        v___x_2938_ = v___x_2890_;
                        v_isShared_2939_ = v_isSharedCheck_2943_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2936_);
                        leanh::lean_dec(v___x_2890_);
                        v___x_2938_ = leanh::lean_box(0);
                        v_isShared_2939_ = v_isSharedCheck_2943_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2897_ = lean_st_ref_take(v___y_2889_);
                v_currNamespace_2898_ = leanh::lean_ctor_get(v_a_2891_, 2);
                leanh::lean_inc(v_currNamespace_2898_);
                leanh::lean_dec(v_a_2891_);
                v_openDecls_2899_ = leanh::lean_ctor_get(v_a_2893_, 3);
                leanh::lean_inc(v_openDecls_2899_);
                leanh::lean_dec(v_a_2893_);
                v_env_2900_ = leanh::lean_ctor_get(v___x_2897_, 0);
                v_messages_2901_ = leanh::lean_ctor_get(v___x_2897_, 1);
                v_scopes_2902_ = leanh::lean_ctor_get(v___x_2897_, 2);
                v_usedQuotCtxts_2903_ = leanh::lean_ctor_get(v___x_2897_, 3);
                v_nextMacroScope_2904_ = leanh::lean_ctor_get(v___x_2897_, 4);
                v_maxRecDepth_2905_ = leanh::lean_ctor_get(v___x_2897_, 5);
                v_ngen_2906_ = leanh::lean_ctor_get(v___x_2897_, 6);
                v_auxDeclNGen_2907_ = leanh::lean_ctor_get(v___x_2897_, 7);
                v_infoState_2908_ = leanh::lean_ctor_get(v___x_2897_, 8);
                v_traceState_2909_ = leanh::lean_ctor_get(v___x_2897_, 9);
                v_snapshotTasks_2910_ = leanh::lean_ctor_get(v___x_2897_, 10);
                v_isSharedCheck_2926_ = (!leanh::lean_is_exclusive(v___x_2897_)) as u8;
                if v_isSharedCheck_2926_ == 0 {
                    v___x_2912_ = v___x_2897_;
                    v_isShared_2913_ = v_isSharedCheck_2926_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2910_);
                    leanh::lean_inc(v_traceState_2909_);
                    leanh::lean_inc(v_infoState_2908_);
                    leanh::lean_inc(v_auxDeclNGen_2907_);
                    leanh::lean_inc(v_ngen_2906_);
                    leanh::lean_inc(v_maxRecDepth_2905_);
                    leanh::lean_inc(v_nextMacroScope_2904_);
                    leanh::lean_inc(v_usedQuotCtxts_2903_);
                    leanh::lean_inc(v_scopes_2902_);
                    leanh::lean_inc(v_messages_2901_);
                    leanh::lean_inc(v_env_2900_);
                    leanh::lean_dec(v___x_2897_);
                    v___x_2912_ = leanh::lean_box(0);
                    v_isShared_2913_ = v_isSharedCheck_2926_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2914_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2914_, 0, v_currNamespace_2898_);
                leanh::lean_ctor_set(v___x_2914_, 1, v_openDecls_2899_);
                v___x_2915_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2915_, 0, v___x_2914_);
                leanh::lean_ctor_set(v___x_2915_, 1, v___y_2885_);
                leanh::lean_inc_ref(v___y_2882_);
                leanh::lean_inc_ref(v___y_2884_);
                v___x_2916_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2916_, 0, v___y_2884_);
                leanh::lean_ctor_set(v___x_2916_, 1, v___y_2887_);
                leanh::lean_ctor_set(v___x_2916_, 2, v___y_2883_);
                leanh::lean_ctor_set(v___x_2916_, 3, v___y_2882_);
                leanh::lean_ctor_set(v___x_2916_, 4, v___x_2915_);
                leanh::lean_ctor_set_uint8(
                    v___x_2916_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2886_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2916_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2888_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2916_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2877_,
                );
                v___x_2917_ = l_Lean_MessageLog_add(v___x_2916_, v_messages_2901_);
                if v_isShared_2913_ == 0 {
                    leanh::lean_ctor_set(v___x_2912_, 1, v___x_2917_);
                    v___x_2919_ = v___x_2912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_env_2900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_scopes_2902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_usedQuotCtxts_2903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_nextMacroScope_2904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 5, v_maxRecDepth_2905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 6, v_ngen_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 7, v_auxDeclNGen_2907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 8, v_infoState_2908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 9, v_traceState_2909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 10, v_snapshotTasks_2910_);
                    v___x_2919_ = v_reuseFailAlloc_2925_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2920_ = lean_st_ref_set(v___y_2889_, v___x_2919_);
                v___x_2921_ = leanh::lean_box(0);
                if v_isShared_2896_ == 0 {
                    leanh::lean_ctor_set(v___x_2895_, 0, v___x_2921_);
                    v___x_2923_ = v___x_2895_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2924_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
                    v___x_2923_ = v_reuseFailAlloc_2924_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2923_;
            }
            6 => {
                if v_isShared_2931_ == 0 {
                    v___x_2933_ = v___x_2930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2933_;
            }
            8 => {
                if v_isShared_2939_ == 0 {
                    v___x_2941_ = v___x_2938_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2941_;
            }
            10 => {
                v_fileName_2950_ = leanh::lean_ctor_get(v___y_2878_, 0);
                v_fileMap_2951_ = leanh::lean_ctor_get(v___y_2878_, 1);
                v_suppressElabErrors_2952_ = leanh::lean_ctor_get_uint8(
                    v___y_2878_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v___x_2953_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2875_,
                    );
                v___x_2954_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v___x_2953_, v___y_2879_);
                v_a_2955_ = leanh::lean_ctor_get(v___x_2954_, 0);
                v_isSharedCheck_2971_ = (!leanh::lean_is_exclusive(v___x_2954_)) as u8;
                if v_isSharedCheck_2971_ == 0 {
                    v___x_2957_ = v___x_2954_;
                    v_isShared_2958_ = v_isSharedCheck_2971_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2955_);
                    leanh::lean_dec(v___x_2954_);
                    v___x_2957_ = leanh::lean_box(0);
                    v_isShared_2958_ = v_isSharedCheck_2971_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc_ref_n(v_fileMap_2951_, 2);
                v___x_2959_ = l_Lean_FileMap_toPosition(v_fileMap_2951_, v___y_2948_);
                leanh::lean_dec(v___y_2948_);
                v___x_2960_ = l_Lean_FileMap_toPosition(v_fileMap_2951_, v___y_2949_);
                leanh::lean_dec(v___y_2949_);
                v___x_2961_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2961_, 0, v___x_2960_);
                v___x_2962_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0;
                if v_suppressElabErrors_2952_ == 0 {
                    leanh::lean_del_object(v___x_2957_);
                    v___y_2882_ = v___x_2962_;
                    v___y_2883_ = v___x_2961_;
                    v___y_2884_ = v_fileName_2950_;
                    v___y_2885_ = v_a_2955_;
                    v___y_2886_ = v___y_2946_;
                    v___y_2887_ = v___x_2959_;
                    v___y_2888_ = v___y_2947_;
                    v___y_2889_ = v___y_2879_;
                    state = 1;
                    continue;
                } else {
                    v___x_2963_ = leanh::lean_box((v___y_2945_) as usize);
                    v___x_2964_ = leanh::lean_box((v_suppressElabErrors_2952_) as usize);
                    v___f_2965_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2965_, 0, v___x_2963_);
                    leanh::lean_closure_set(v___f_2965_, 1, v___x_2964_);
                    leanh::lean_inc(v_a_2955_);
                    v___x_2966_ = l_Lean_MessageData_hasTag(v___f_2965_, v_a_2955_);
                    if v___x_2966_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2961_, 1);
                        leanh::lean_dec_ref(v___x_2959_);
                        leanh::lean_dec(v_a_2955_);
                        v___x_2967_ = leanh::lean_box(0);
                        if v_isShared_2958_ == 0 {
                            leanh::lean_ctor_set(v___x_2957_, 0, v___x_2967_);
                            v___x_2969_ = v___x_2957_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2970_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
                            v___x_2969_ = v_reuseFailAlloc_2970_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2957_);
                        v___y_2882_ = v___x_2962_;
                        v___y_2883_ = v___x_2961_;
                        v___y_2884_ = v_fileName_2950_;
                        v___y_2885_ = v_a_2955_;
                        v___y_2886_ = v___y_2946_;
                        v___y_2887_ = v___x_2959_;
                        v___y_2888_ = v___y_2947_;
                        v___y_2889_ = v___y_2879_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_2969_;
            }
            13 => {
                v___x_2978_ = l_Lean_Syntax_getTailPos_x3f(v___y_2974_, v___y_2975_);
                leanh::lean_dec(v___y_2974_);
                if leanh::lean_obj_tag(v___x_2978_) == 0 {
                    leanh::lean_inc(v___y_2977_);
                    v___y_2945_ = v___y_2973_;
                    v___y_2946_ = v___y_2975_;
                    v___y_2947_ = v___y_2976_;
                    v___y_2948_ = v___y_2977_;
                    v___y_2949_ = v___y_2977_;
                    state = 10;
                    continue;
                } else {
                    v_val_2979_ = leanh::lean_ctor_get(v___x_2978_, 0);
                    leanh::lean_inc(v_val_2979_);
                    leanh::lean_dec_ref_known(v___x_2978_, 1);
                    v___y_2945_ = v___y_2973_;
                    v___y_2946_ = v___y_2975_;
                    v___y_2947_ = v___y_2976_;
                    v___y_2948_ = v___y_2977_;
                    v___y_2949_ = v_val_2979_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_2984_ = l_Lean_Elab_Command_getRef___redArg(v___y_2878_);
                if leanh::lean_obj_tag(v___x_2984_) == 0 {
                    v_a_2985_ = leanh::lean_ctor_get(v___x_2984_, 0);
                    leanh::lean_inc(v_a_2985_);
                    leanh::lean_dec_ref_known(v___x_2984_, 1);
                    v_ref_2986_ = l_Lean_replaceRef(v_ref_2874_, v_a_2985_);
                    leanh::lean_dec(v_a_2985_);
                    v___x_2987_ = l_Lean_Syntax_getPos_x3f(v_ref_2986_, v___y_2982_);
                    if leanh::lean_obj_tag(v___x_2987_) == 0 {
                        v___x_2988_ = leanh::lean_unsigned_to_nat(0);
                        v___y_2973_ = v___y_2981_;
                        v___y_2974_ = v_ref_2986_;
                        v___y_2975_ = v___y_2982_;
                        v___y_2976_ = v___y_2983_;
                        v___y_2977_ = v___x_2988_;
                        state = 13;
                        continue;
                    } else {
                        v_val_2989_ = leanh::lean_ctor_get(v___x_2987_, 0);
                        leanh::lean_inc(v_val_2989_);
                        leanh::lean_dec_ref_known(v___x_2987_, 1);
                        v___y_2973_ = v___y_2981_;
                        v___y_2974_ = v_ref_2986_;
                        v___y_2975_ = v___y_2982_;
                        v___y_2976_ = v___y_2983_;
                        v___y_2977_ = v_val_2989_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2875_);
                    v_a_2990_ = leanh::lean_ctor_get(v___x_2984_, 0);
                    v_isSharedCheck_2997_ = (!leanh::lean_is_exclusive(v___x_2984_)) as u8;
                    if v_isSharedCheck_2997_ == 0 {
                        v___x_2992_ = v___x_2984_;
                        v_isShared_2993_ = v_isSharedCheck_2997_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2990_);
                        leanh::lean_dec(v___x_2984_);
                        v___x_2992_ = leanh::lean_box(0);
                        v_isShared_2993_ = v_isSharedCheck_2997_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_2993_ == 0 {
                    v___x_2995_ = v___x_2992_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
                    v___x_2995_ = v_reuseFailAlloc_2996_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2995_;
            }
            17 => {
                if v___y_3002_ == 0 {
                    v___y_2981_ = v___y_3000_;
                    v___y_2982_ = v___y_3001_;
                    v___y_2983_ = v_severity_2876_;
                    state = 14;
                    continue;
                } else {
                    v___y_2981_ = v___y_3000_;
                    v___y_2982_ = v___y_3001_;
                    v___y_2983_ = v___x_2998_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_3004_ == 0 {
                    v___x_3005_ = lean_st_ref_get(v___y_2879_);
                    v_scopes_3006_ = leanh::lean_ctor_get(v___x_3005_, 2);
                    leanh::lean_inc(v_scopes_3006_);
                    leanh::lean_dec(v___x_3005_);
                    v___x_3007_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_3008_ = l_List_head_x21___redArg(v___x_3007_, v_scopes_3006_);
                    leanh::lean_dec(v_scopes_3006_);
                    v_opts_3009_ = leanh::lean_ctor_get(v___x_3008_, 1);
                    leanh::lean_inc_ref(v_opts_3009_);
                    leanh::lean_dec(v___x_3008_);
                    v___x_3010_ = 1;
                    v___x_3011_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2876_, v___x_3010_);
                    if v___x_3011_ == 0 {
                        leanh::lean_dec_ref(v_opts_3009_);
                        v___y_3000_ = v___y_3004_;
                        v___y_3001_ = v___y_3004_;
                        v___y_3002_ = v___x_3011_;
                        state = 17;
                        continue;
                    } else {
                        v___x_3012_ = l_Lean_warningAsError;
                        v___x_3013_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(v_opts_3009_, v___x_3012_);
                        leanh::lean_dec_ref(v_opts_3009_);
                        v___y_3000_ = v___y_3004_;
                        v___y_3001_ = v___y_3004_;
                        v___y_3002_ = v___x_3013_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2875_);
                    v___x_3014_ = leanh::lean_box(0);
                    v___x_3015_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3015_, 0, v___x_3014_);
                    return v___x_3015_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___boxed(
    mut v_ref_3018_: *mut leanh::LeanObject,
    mut v_msgData_3019_: *mut leanh::LeanObject,
    mut v_severity_3020_: *mut leanh::LeanObject,
    mut v_isSilent_3021_: *mut leanh::LeanObject,
    mut v___y_3022_: *mut leanh::LeanObject,
    mut v___y_3023_: *mut leanh::LeanObject,
    mut v___y_3024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_3025_: u8 = 0;
    let mut v_isSilent_boxed_3026_: u8 = 0;
    let mut v_res_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3025_ = (leanh::lean_unbox(v_severity_3020_) as u8);
    v_isSilent_boxed_3026_ = (leanh::lean_unbox(v_isSilent_3021_) as u8);
    v_res_3027_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_3018_, v_msgData_3019_, v_severity_boxed_3025_, v_isSilent_boxed_3026_, v___y_3022_, v___y_3023_);
    leanh::lean_dec(v___y_3023_);
    leanh::lean_dec_ref(v___y_3022_);
    leanh::lean_dec(v_ref_3018_);
    return v_res_3027_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(
    mut v_ref_3028_: *mut leanh::LeanObject,
    mut v_msgData_3029_: *mut leanh::LeanObject,
    mut v___y_3030_: *mut leanh::LeanObject,
    mut v___y_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3033_: u8 = 0;
    let mut v___x_3034_: u8 = 0;
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3033_ = 0;
    v___x_3034_ = 0;
    v___x_3035_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_3028_, v_msgData_3029_, v___x_3033_, v___x_3034_, v___y_3030_, v___y_3031_);
    return v___x_3035_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1___boxed(
    mut v_ref_3036_: *mut leanh::LeanObject,
    mut v_msgData_3037_: *mut leanh::LeanObject,
    mut v___y_3038_: *mut leanh::LeanObject,
    mut v___y_3039_: *mut leanh::LeanObject,
    mut v___y_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3041_ = l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(
        v_ref_3036_,
        v_msgData_3037_,
        v___y_3038_,
        v___y_3039_,
    );
    leanh::lean_dec(v___y_3039_);
    leanh::lean_dec_ref(v___y_3038_);
    leanh::lean_dec(v_ref_3036_);
    return v_res_3041_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3042_ = leanh::lean_box(1);
    v___x_3043_ = l_Lean_MessageData_ofFormat(v___x_3042_);
    return v___x_3043_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3047_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__2;
    v___x_3048_ = l_Lean_MessageData_ofFormat(v___x_3047_);
    return v___x_3048_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14(
    mut v_x_3049_: *mut leanh::LeanObject,
    mut v_x_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3055_: u8 = 0;
    let mut v_before_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_unused_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3050_) == 0 {
                    return v_x_3049_;
                } else {
                    v_head_3051_ = leanh::lean_ctor_get(v_x_3050_, 0);
                    v_tail_3052_ = leanh::lean_ctor_get(v_x_3050_, 1);
                    v_isSharedCheck_3074_ = (!leanh::lean_is_exclusive(v_x_3050_)) as u8;
                    if v_isSharedCheck_3074_ == 0 {
                        v___x_3054_ = v_x_3050_;
                        v_isShared_3055_ = v_isSharedCheck_3074_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3052_);
                        leanh::lean_inc(v_head_3051_);
                        leanh::lean_dec(v_x_3050_);
                        v___x_3054_ = leanh::lean_box(0);
                        v_isShared_3055_ = v_isSharedCheck_3074_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3056_ = leanh::lean_ctor_get(v_head_3051_, 0);
                v_isSharedCheck_3072_ = (!leanh::lean_is_exclusive(v_head_3051_)) as u8;
                if v_isSharedCheck_3072_ == 0 {
                    v_unused_3073_ = leanh::lean_ctor_get(v_head_3051_, 1);
                    leanh::lean_dec(v_unused_3073_);
                    v___x_3058_ = v_head_3051_;
                    v_isShared_3059_ = v_isSharedCheck_3072_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_3056_);
                    leanh::lean_dec(v_head_3051_);
                    v___x_3058_ = leanh::lean_box(0);
                    v_isShared_3059_ = v_isSharedCheck_3072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3060_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0);
                if v_isShared_3059_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3058_, 7);
                    leanh::lean_ctor_set(v___x_3058_, 1, v___x_3060_);
                    leanh::lean_ctor_set(v___x_3058_, 0, v_x_3049_);
                    v___x_3062_ = v___x_3058_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3071_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_x_3049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3060_);
                    v___x_3062_ = v_reuseFailAlloc_3071_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3063_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__3);
                if v_isShared_3055_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3054_, 7);
                    leanh::lean_ctor_set(v___x_3054_, 1, v___x_3063_);
                    leanh::lean_ctor_set(v___x_3054_, 0, v___x_3062_);
                    v___x_3065_ = v___x_3054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_3063_);
                    v___x_3065_ = v_reuseFailAlloc_3070_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3066_ = l_Lean_MessageData_ofSyntax(v_before_3056_);
                v___x_3067_ = l_Lean_indentD(v___x_3066_);
                v___x_3068_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3068_, 0, v___x_3065_);
                leanh::lean_ctor_set(v___x_3068_, 1, v___x_3067_);
                v_x_3049_ = v___x_3068_;
                v_x_3050_ = v_tail_3052_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3078_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__1;
    v___x_3079_ = l_Lean_MessageData_ofFormat(v___x_3078_);
    return v___x_3079_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(
    mut v_msgData_3080_: *mut leanh::LeanObject,
    mut v_macroStack_3081_: *mut leanh::LeanObject,
    mut v___y_3082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut v_unused_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3084_ = lean_st_ref_get(v___y_3082_);
                v_scopes_3085_ = leanh::lean_ctor_get(v___x_3084_, 2);
                leanh::lean_inc(v_scopes_3085_);
                leanh::lean_dec(v___x_3084_);
                v___x_3086_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3087_ = l_List_head_x21___redArg(v___x_3086_, v_scopes_3085_);
                leanh::lean_dec(v_scopes_3085_);
                v_opts_3088_ = leanh::lean_ctor_get(v___x_3087_, 1);
                leanh::lean_inc_ref(v_opts_3088_);
                leanh::lean_dec(v___x_3087_);
                v___x_3089_ = l_Lean_Elab_pp_macroStack;
                v___x_3090_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__6(v_opts_3088_, v___x_3089_);
                leanh::lean_dec_ref(v_opts_3088_);
                if v___x_3090_ == 0 {
                    leanh::lean_dec(v_macroStack_3081_);
                    v___x_3091_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3091_, 0, v_msgData_3080_);
                    return v___x_3091_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_3081_) == 0 {
                        v___x_3092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3092_, 0, v_msgData_3080_);
                        return v___x_3092_;
                    } else {
                        v_head_3093_ = leanh::lean_ctor_get(v_macroStack_3081_, 0);
                        leanh::lean_inc(v_head_3093_);
                        v_after_3094_ = leanh::lean_ctor_get(v_head_3093_, 1);
                        v_isSharedCheck_3109_ =
                            (!leanh::lean_is_exclusive(v_head_3093_)) as u8;
                        if v_isSharedCheck_3109_ == 0 {
                            v_unused_3110_ = leanh::lean_ctor_get(v_head_3093_, 0);
                            leanh::lean_dec(v_unused_3110_);
                            v___x_3096_ = v_head_3093_;
                            v_isShared_3097_ = v_isSharedCheck_3109_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_3094_);
                            leanh::lean_dec(v_head_3093_);
                            v___x_3096_ = leanh::lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3109_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3098_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14___closed__0);
                if v_isShared_3097_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3096_, 7);
                    leanh::lean_ctor_set(v___x_3096_, 1, v___x_3098_);
                    leanh::lean_ctor_set(v___x_3096_, 0, v_msgData_3080_);
                    v___x_3100_ = v___x_3096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_msgData_3080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3098_);
                    v___x_3100_ = v_reuseFailAlloc_3108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3101_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___closed__2);
                v___x_3102_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3102_, 0, v___x_3100_);
                leanh::lean_ctor_set(v___x_3102_, 1, v___x_3101_);
                v___x_3103_ = l_Lean_MessageData_ofSyntax(v_after_3094_);
                v___x_3104_ = l_Lean_indentD(v___x_3103_);
                v_msgData_3105_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_3105_, 0, v___x_3102_);
                leanh::lean_ctor_set(v_msgData_3105_, 1, v___x_3104_);
                v___x_3106_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13_spec__14(v_msgData_3105_, v_macroStack_3081_);
                v___x_3107_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3107_, 0, v___x_3106_);
                return v___x_3107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg___boxed(
    mut v_msgData_3111_: *mut leanh::LeanObject,
    mut v_macroStack_3112_: *mut leanh::LeanObject,
    mut v___y_3113_: *mut leanh::LeanObject,
    mut v___y_3114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3115_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(v_msgData_3111_, v_macroStack_3112_, v___y_3113_);
    leanh::lean_dec(v___y_3113_);
    return v_res_3115_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(
    mut v_msg_3116_: *mut leanh::LeanObject,
    mut v___y_3117_: *mut leanh::LeanObject,
    mut v___y_3118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v_a_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3139_: u8 = 0;
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3120_ = l_Lean_Elab_Command_getRef___redArg(v___y_3117_);
                if leanh::lean_obj_tag(v___x_3120_) == 0 {
                    v_a_3121_ = leanh::lean_ctor_get(v___x_3120_, 0);
                    leanh::lean_inc(v_a_3121_);
                    leanh::lean_dec_ref_known(v___x_3120_, 1);
                    v_macroStack_3122_ = leanh::lean_ctor_get(v___y_3117_, 4);
                    v___x_3123_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v_msg_3116_, v___y_3118_);
                    v_a_3124_ = leanh::lean_ctor_get(v___x_3123_, 0);
                    leanh::lean_inc(v_a_3124_);
                    leanh::lean_dec_ref(v___x_3123_);
                    v___x_3125_ = l_Lean_Elab_getBetterRef(v_a_3121_, v_macroStack_3122_);
                    leanh::lean_dec(v_a_3121_);
                    leanh::lean_inc(v_macroStack_3122_);
                    v___x_3126_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(v_a_3124_, v_macroStack_3122_, v___y_3118_);
                    v_a_3127_ = leanh::lean_ctor_get(v___x_3126_, 0);
                    v_isSharedCheck_3135_ = (!leanh::lean_is_exclusive(v___x_3126_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3129_ = v___x_3126_;
                        v_isShared_3130_ = v_isSharedCheck_3135_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3127_);
                        leanh::lean_dec(v___x_3126_);
                        v___x_3129_ = leanh::lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3135_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_3116_);
                    v_a_3136_ = leanh::lean_ctor_get(v___x_3120_, 0);
                    v_isSharedCheck_3143_ = (!leanh::lean_is_exclusive(v___x_3120_)) as u8;
                    if v_isSharedCheck_3143_ == 0 {
                        v___x_3138_ = v___x_3120_;
                        v_isShared_3139_ = v_isSharedCheck_3143_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3136_);
                        leanh::lean_dec(v___x_3120_);
                        v___x_3138_ = leanh::lean_box(0);
                        v_isShared_3139_ = v_isSharedCheck_3143_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3131_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3131_, 0, v___x_3125_);
                leanh::lean_ctor_set(v___x_3131_, 1, v_a_3127_);
                if v_isShared_3130_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3129_, 1);
                    leanh::lean_ctor_set(v___x_3129_, 0, v___x_3131_);
                    v___x_3133_ = v___x_3129_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3133_;
            }
            3 => {
                if v_isShared_3139_ == 0 {
                    v___x_3141_ = v___x_3138_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg___boxed(
    mut v_msg_3144_: *mut leanh::LeanObject,
    mut v___y_3145_: *mut leanh::LeanObject,
    mut v___y_3146_: *mut leanh::LeanObject,
    mut v___y_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(v_msg_3144_, v___y_3145_, v___y_3146_);
    leanh::lean_dec(v___y_3146_);
    leanh::lean_dec_ref(v___y_3145_);
    return v_res_3148_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(
    mut v_ref_3149_: *mut leanh::LeanObject,
    mut v_msg_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3165_: u8 = 0;
    let mut v_ref_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3154_ = l_Lean_Elab_Command_getRef___redArg(v___y_3151_);
                if leanh::lean_obj_tag(v___x_3154_) == 0 {
                    v_a_3155_ = leanh::lean_ctor_get(v___x_3154_, 0);
                    leanh::lean_inc(v_a_3155_);
                    leanh::lean_dec_ref_known(v___x_3154_, 1);
                    v_fileName_3156_ = leanh::lean_ctor_get(v___y_3151_, 0);
                    v_fileMap_3157_ = leanh::lean_ctor_get(v___y_3151_, 1);
                    v_currRecDepth_3158_ = leanh::lean_ctor_get(v___y_3151_, 2);
                    v_cmdPos_3159_ = leanh::lean_ctor_get(v___y_3151_, 3);
                    v_macroStack_3160_ = leanh::lean_ctor_get(v___y_3151_, 4);
                    v_quotContext_x3f_3161_ = leanh::lean_ctor_get(v___y_3151_, 5);
                    v_currMacroScope_3162_ = leanh::lean_ctor_get(v___y_3151_, 6);
                    v_snap_x3f_3163_ = leanh::lean_ctor_get(v___y_3151_, 8);
                    v_cancelTk_x3f_3164_ = leanh::lean_ctor_get(v___y_3151_, 9);
                    v_suppressElabErrors_3165_ = leanh::lean_ctor_get_uint8(
                        v___y_3151_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_3166_ = l_Lean_replaceRef(v_ref_3149_, v_a_3155_);
                    leanh::lean_dec(v_a_3155_);
                    leanh::lean_inc(v_cancelTk_x3f_3164_);
                    leanh::lean_inc(v_snap_x3f_3163_);
                    leanh::lean_inc(v_currMacroScope_3162_);
                    leanh::lean_inc(v_quotContext_x3f_3161_);
                    leanh::lean_inc(v_macroStack_3160_);
                    leanh::lean_inc(v_cmdPos_3159_);
                    leanh::lean_inc(v_currRecDepth_3158_);
                    leanh::lean_inc_ref(v_fileMap_3157_);
                    leanh::lean_inc_ref(v_fileName_3156_);
                    v___x_3167_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    leanh::lean_ctor_set(v___x_3167_, 0, v_fileName_3156_);
                    leanh::lean_ctor_set(v___x_3167_, 1, v_fileMap_3157_);
                    leanh::lean_ctor_set(v___x_3167_, 2, v_currRecDepth_3158_);
                    leanh::lean_ctor_set(v___x_3167_, 3, v_cmdPos_3159_);
                    leanh::lean_ctor_set(v___x_3167_, 4, v_macroStack_3160_);
                    leanh::lean_ctor_set(v___x_3167_, 5, v_quotContext_x3f_3161_);
                    leanh::lean_ctor_set(v___x_3167_, 6, v_currMacroScope_3162_);
                    leanh::lean_ctor_set(v___x_3167_, 7, v_ref_3166_);
                    leanh::lean_ctor_set(v___x_3167_, 8, v_snap_x3f_3163_);
                    leanh::lean_ctor_set(v___x_3167_, 9, v_cancelTk_x3f_3164_);
                    leanh::lean_ctor_set_uint8(
                        v___x_3167_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_3165_,
                    );
                    v___x_3168_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(v_msg_3150_, v___x_3167_, v___y_3152_);
                    leanh::lean_dec_ref_known(v___x_3167_, 10);
                    return v___x_3168_;
                } else {
                    leanh::lean_dec_ref(v_msg_3150_);
                    v_a_3169_ = leanh::lean_ctor_get(v___x_3154_, 0);
                    v_isSharedCheck_3176_ = (!leanh::lean_is_exclusive(v___x_3154_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3171_ = v___x_3154_;
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3169_);
                        leanh::lean_dec(v___x_3154_);
                        v___x_3171_ = leanh::lean_box(0);
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3172_ == 0 {
                    v___x_3174_ = v___x_3171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg___boxed(
    mut v_ref_3177_: *mut leanh::LeanObject,
    mut v_msg_3178_: *mut leanh::LeanObject,
    mut v___y_3179_: *mut leanh::LeanObject,
    mut v___y_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3182_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(v_ref_3177_, v_msg_3178_, v___y_3179_, v___y_3180_);
    leanh::lean_dec(v___y_3180_);
    leanh::lean_dec_ref(v___y_3179_);
    leanh::lean_dec(v_ref_3177_);
    return v_res_3182_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3184_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__0;
    v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
    return v___x_3185_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3187_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__2;
    v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
    return v___x_3188_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__4;
    v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
    return v___x_3191_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3193_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__6;
    v___x_3194_ = l_Lean_stringToMessageData(v___x_3193_);
    return v___x_3194_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3196_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__8;
    v___x_3197_ = l_Lean_stringToMessageData(v___x_3196_);
    return v___x_3197_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3199_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__10;
    v___x_3200_ = l_Lean_stringToMessageData(v___x_3199_);
    return v___x_3200_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__12;
    v___x_3203_ = l_Lean_stringToMessageData(v___x_3202_);
    return v___x_3203_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(
    mut v_msg_3204_: *mut leanh::LeanObject,
    mut v_declHint_3205_: *mut leanh::LeanObject,
    mut v___y_3206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: u8 = 0;
    let mut v_isExporting_3211_: u8 = 0;
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3233_: u8 = 0;
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3208_ = lean_st_ref_get(v___y_3206_);
                v_env_3209_ = leanh::lean_ctor_get(v___x_3208_, 0);
                leanh::lean_inc_ref(v_env_3209_);
                leanh::lean_dec(v___x_3208_);
                v___x_3210_ = l_Lean_Name_isAnonymous(v_declHint_3205_);
                if v___x_3210_ == 0 {
                    v_isExporting_3211_ = leanh::lean_ctor_get_uint8(
                        v_env_3209_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3211_ == 0 {
                        leanh::lean_dec_ref(v_env_3209_);
                        leanh::lean_dec(v_declHint_3205_);
                        v___x_3212_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3212_, 0, v_msg_3204_);
                        return v___x_3212_;
                    } else {
                        leanh::lean_inc_ref(v_env_3209_);
                        v___x_3213_ = l_Lean_Environment_setExporting(v_env_3209_, v___x_3210_);
                        leanh::lean_inc(v_declHint_3205_);
                        leanh::lean_inc_ref(v___x_3213_);
                        v___x_3214_ = l_Lean_Environment_contains(
                            v___x_3213_,
                            v_declHint_3205_,
                            v_isExporting_3211_,
                        );
                        if v___x_3214_ == 0 {
                            leanh::lean_dec_ref(v___x_3213_);
                            leanh::lean_dec_ref(v_env_3209_);
                            leanh::lean_dec(v_declHint_3205_);
                            v___x_3215_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3215_, 0, v_msg_3204_);
                            return v___x_3215_;
                        } else {
                            v___x_3216_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__2);
                            v___x_3217_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg___closed__5);
                            v___x_3218_ = l_Lean_Options_empty;
                            v___x_3219_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3219_, 0, v___x_3213_);
                            leanh::lean_ctor_set(v___x_3219_, 1, v___x_3216_);
                            leanh::lean_ctor_set(v___x_3219_, 2, v___x_3217_);
                            leanh::lean_ctor_set(v___x_3219_, 3, v___x_3218_);
                            leanh::lean_inc(v_declHint_3205_);
                            v___x_3220_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3205_, v___x_3210_);
                            v_c_3221_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3221_, 0, v___x_3219_);
                            leanh::lean_ctor_set(v_c_3221_, 1, v___x_3220_);
                            v___x_3222_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3209_,
                                v_declHint_3205_,
                            );
                            if leanh::lean_obj_tag(v___x_3222_) == 0 {
                                leanh::lean_dec_ref(v_env_3209_);
                                leanh::lean_dec(v_declHint_3205_);
                                v___x_3223_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1);
                                v___x_3224_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3224_, 0, v___x_3223_);
                                leanh::lean_ctor_set(v___x_3224_, 1, v_c_3221_);
                                v___x_3225_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__3);
                                v___x_3226_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3226_, 0, v___x_3224_);
                                leanh::lean_ctor_set(v___x_3226_, 1, v___x_3225_);
                                v___x_3227_ = l_Lean_MessageData_note(v___x_3226_);
                                v___x_3228_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3228_, 0, v_msg_3204_);
                                leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
                                v___x_3229_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3229_, 0, v___x_3228_);
                                return v___x_3229_;
                            } else {
                                v_val_3230_ = leanh::lean_ctor_get(v___x_3222_, 0);
                                v_isSharedCheck_3265_ =
                                    (!leanh::lean_is_exclusive(v___x_3222_)) as u8;
                                if v_isSharedCheck_3265_ == 0 {
                                    v___x_3232_ = v___x_3222_;
                                    v_isShared_3233_ = v_isSharedCheck_3265_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3230_);
                                    leanh::lean_dec(v___x_3222_);
                                    v___x_3232_ = leanh::lean_box(0);
                                    v_isShared_3233_ = v_isSharedCheck_3265_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3209_);
                    leanh::lean_dec(v_declHint_3205_);
                    v___x_3266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3266_, 0, v_msg_3204_);
                    return v___x_3266_;
                }
            }
            1 => {
                v___x_3234_ = leanh::lean_box(0);
                v___x_3235_ = l_Lean_Environment_header(v_env_3209_);
                leanh::lean_dec_ref(v_env_3209_);
                v___x_3236_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3235_);
                v_mod_3237_ = lean_array_get(v___x_3234_, v___x_3236_, v_val_3230_);
                leanh::lean_dec(v_val_3230_);
                leanh::lean_dec_ref(v___x_3236_);
                v___x_3238_ = l_Lean_isPrivateName(v_declHint_3205_);
                leanh::lean_dec(v_declHint_3205_);
                if v___x_3238_ == 0 {
                    v___x_3239_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__5);
                    v___x_3240_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3240_, 0, v___x_3239_);
                    leanh::lean_ctor_set(v___x_3240_, 1, v_c_3221_);
                    v___x_3241_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__7);
                    v___x_3242_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3242_, 0, v___x_3240_);
                    leanh::lean_ctor_set(v___x_3242_, 1, v___x_3241_);
                    v___x_3243_ = l_Lean_MessageData_ofName(v_mod_3237_);
                    v___x_3244_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3244_, 0, v___x_3242_);
                    leanh::lean_ctor_set(v___x_3244_, 1, v___x_3243_);
                    v___x_3245_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__9);
                    v___x_3246_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3246_, 0, v___x_3244_);
                    leanh::lean_ctor_set(v___x_3246_, 1, v___x_3245_);
                    v___x_3247_ = l_Lean_MessageData_note(v___x_3246_);
                    v___x_3248_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3248_, 0, v_msg_3204_);
                    leanh::lean_ctor_set(v___x_3248_, 1, v___x_3247_);
                    if v_isShared_3233_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3232_, 0);
                        leanh::lean_ctor_set(v___x_3232_, 0, v___x_3248_);
                        v___x_3250_ = v___x_3232_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
                        v___x_3250_ = v_reuseFailAlloc_3251_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3252_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__1);
                    v___x_3253_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3253_, 0, v___x_3252_);
                    leanh::lean_ctor_set(v___x_3253_, 1, v_c_3221_);
                    v___x_3254_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__11);
                    v___x_3255_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3255_, 0, v___x_3253_);
                    leanh::lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                    v___x_3256_ = l_Lean_MessageData_ofName(v_mod_3237_);
                    v___x_3257_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3257_, 0, v___x_3255_);
                    leanh::lean_ctor_set(v___x_3257_, 1, v___x_3256_);
                    v___x_3258_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___closed__13);
                    v___x_3259_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3259_, 0, v___x_3257_);
                    leanh::lean_ctor_set(v___x_3259_, 1, v___x_3258_);
                    v___x_3260_ = l_Lean_MessageData_note(v___x_3259_);
                    v___x_3261_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3261_, 0, v_msg_3204_);
                    leanh::lean_ctor_set(v___x_3261_, 1, v___x_3260_);
                    if v_isShared_3233_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3232_, 0);
                        leanh::lean_ctor_set(v___x_3232_, 0, v___x_3261_);
                        v___x_3263_ = v___x_3232_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
                        v___x_3263_ = v_reuseFailAlloc_3264_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3250_;
            }
            3 => {
                return v___x_3263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg___boxed(
    mut v_msg_3267_: *mut leanh::LeanObject,
    mut v_declHint_3268_: *mut leanh::LeanObject,
    mut v___y_3269_: *mut leanh::LeanObject,
    mut v___y_3270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3271_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_3267_, v_declHint_3268_, v___y_3269_);
    leanh::lean_dec(v___y_3269_);
    return v_res_3271_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9(
    mut v_msg_3272_: *mut leanh::LeanObject,
    mut v_declHint_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3277_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_3272_, v_declHint_3273_, v___y_3275_);
                v_a_3278_ = leanh::lean_ctor_get(v___x_3277_, 0);
                v_isSharedCheck_3287_ = (!leanh::lean_is_exclusive(v___x_3277_)) as u8;
                if v_isSharedCheck_3287_ == 0 {
                    v___x_3280_ = v___x_3277_;
                    v_isShared_3281_ = v_isSharedCheck_3287_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3278_);
                    leanh::lean_dec(v___x_3277_);
                    v___x_3280_ = leanh::lean_box(0);
                    v_isShared_3281_ = v_isSharedCheck_3287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3282_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3283_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3283_, 0, v___x_3282_);
                leanh::lean_ctor_set(v___x_3283_, 1, v_a_3278_);
                if v_isShared_3281_ == 0 {
                    leanh::lean_ctor_set(v___x_3280_, 0, v___x_3283_);
                    v___x_3285_ = v___x_3280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
                    v___x_3285_ = v_reuseFailAlloc_3286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9___boxed(
    mut v_msg_3288_: *mut leanh::LeanObject,
    mut v_declHint_3289_: *mut leanh::LeanObject,
    mut v___y_3290_: *mut leanh::LeanObject,
    mut v___y_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3293_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9(v_msg_3288_, v_declHint_3289_, v___y_3290_, v___y_3291_);
    leanh::lean_dec(v___y_3291_);
    leanh::lean_dec_ref(v___y_3290_);
    return v_res_3293_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(
    mut v_ref_3294_: *mut leanh::LeanObject,
    mut v_msg_3295_: *mut leanh::LeanObject,
    mut v_declHint_3296_: *mut leanh::LeanObject,
    mut v___y_3297_: *mut leanh::LeanObject,
    mut v___y_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3300_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9(v_msg_3295_, v_declHint_3296_, v___y_3297_, v___y_3298_);
    v_a_3301_ = leanh::lean_ctor_get(v___x_3300_, 0);
    leanh::lean_inc(v_a_3301_);
    leanh::lean_dec_ref(v___x_3300_);
    v___x_3302_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(v_ref_3294_, v_a_3301_, v___y_3297_, v___y_3298_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_ref_3303_: *mut leanh::LeanObject,
    mut v_msg_3304_: *mut leanh::LeanObject,
    mut v_declHint_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
    mut v___y_3307_: *mut leanh::LeanObject,
    mut v___y_3308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3309_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_3303_, v_msg_3304_, v_declHint_3305_, v___y_3306_, v___y_3307_);
    leanh::lean_dec(v___y_3307_);
    leanh::lean_dec_ref(v___y_3306_);
    leanh::lean_dec(v_ref_3303_);
    return v_res_3309_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
    v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
    return v___x_3312_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__2;
    v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_3316_: *mut leanh::LeanObject,
    mut v_constName_3317_: *mut leanh::LeanObject,
    mut v___y_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
    v___x_3322_ = 0;
    leanh::lean_inc(v_constName_3317_);
    v___x_3323_ = l_Lean_MessageData_ofConstName(v_constName_3317_, v___x_3322_);
    v___x_3324_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3324_, 0, v___x_3321_);
    leanh::lean_ctor_set(v___x_3324_, 1, v___x_3323_);
    v___x_3325_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___closed__3);
    v___x_3326_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3326_, 0, v___x_3324_);
    leanh::lean_ctor_set(v___x_3326_, 1, v___x_3325_);
    v___x_3327_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_3316_, v___x_3326_, v_constName_3317_, v___y_3318_, v___y_3319_);
    return v___x_3327_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_3328_: *mut leanh::LeanObject,
    mut v_constName_3329_: *mut leanh::LeanObject,
    mut v___y_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3328_, v_constName_3329_, v___y_3330_, v___y_3331_);
    leanh::lean_dec(v___y_3331_);
    leanh::lean_dec_ref(v___y_3330_);
    leanh::lean_dec(v_ref_3328_);
    return v_res_3333_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(
    mut v_constName_3334_: *mut leanh::LeanObject,
    mut v___y_3335_: *mut leanh::LeanObject,
    mut v___y_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3338_ = l_Lean_Elab_Command_getRef___redArg(v___y_3335_);
                if leanh::lean_obj_tag(v___x_3338_) == 0 {
                    v_a_3339_ = leanh::lean_ctor_get(v___x_3338_, 0);
                    leanh::lean_inc(v_a_3339_);
                    leanh::lean_dec_ref_known(v___x_3338_, 1);
                    v___x_3340_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(v_a_3339_, v_constName_3334_, v___y_3335_, v___y_3336_);
                    leanh::lean_dec(v_a_3339_);
                    return v___x_3340_;
                } else {
                    leanh::lean_dec(v_constName_3334_);
                    v_a_3341_ = leanh::lean_ctor_get(v___x_3338_, 0);
                    v_isSharedCheck_3348_ = (!leanh::lean_is_exclusive(v___x_3338_)) as u8;
                    if v_isSharedCheck_3348_ == 0 {
                        v___x_3343_ = v___x_3338_;
                        v_isShared_3344_ = v_isSharedCheck_3348_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3341_);
                        leanh::lean_dec(v___x_3338_);
                        v___x_3343_ = leanh::lean_box(0);
                        v_isShared_3344_ = v_isSharedCheck_3348_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3344_ == 0 {
                    v___x_3346_ = v___x_3343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3347_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
                    v___x_3346_ = v_reuseFailAlloc_3347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_3349_: *mut leanh::LeanObject,
    mut v___y_3350_: *mut leanh::LeanObject,
    mut v___y_3351_: *mut leanh::LeanObject,
    mut v___y_3352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(v_constName_3349_, v___y_3350_, v___y_3351_);
    leanh::lean_dec(v___y_3351_);
    leanh::lean_dec_ref(v___y_3350_);
    return v_res_3353_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0(
    mut v_constName_3354_: *mut leanh::LeanObject,
    mut v___y_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3366_: u8 = 0;
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3358_ = lean_st_ref_get(v___y_3356_);
                v_env_3359_ = leanh::lean_ctor_get(v___x_3358_, 0);
                leanh::lean_inc_ref(v_env_3359_);
                leanh::lean_dec(v___x_3358_);
                v___x_3360_ = 0;
                leanh::lean_inc(v_constName_3354_);
                v___x_3361_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_3359_,
                    v_constName_3354_,
                    v___x_3360_,
                );
                if leanh::lean_obj_tag(v___x_3361_) == 0 {
                    v___x_3362_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(v_constName_3354_, v___y_3355_, v___y_3356_);
                    return v___x_3362_;
                } else {
                    leanh::lean_dec(v_constName_3354_);
                    v_val_3363_ = leanh::lean_ctor_get(v___x_3361_, 0);
                    v_isSharedCheck_3370_ = (!leanh::lean_is_exclusive(v___x_3361_)) as u8;
                    if v_isSharedCheck_3370_ == 0 {
                        v___x_3365_ = v___x_3361_;
                        v_isShared_3366_ = v_isSharedCheck_3370_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3363_);
                        leanh::lean_dec(v___x_3361_);
                        v___x_3365_ = leanh::lean_box(0);
                        v_isShared_3366_ = v_isSharedCheck_3370_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3366_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3365_, 0);
                    v___x_3368_ = v___x_3365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_val_3363_);
                    v___x_3368_ = v_reuseFailAlloc_3369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0___boxed(
    mut v_constName_3371_: *mut leanh::LeanObject,
    mut v___y_3372_: *mut leanh::LeanObject,
    mut v___y_3373_: *mut leanh::LeanObject,
    mut v___y_3374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3375_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0(v_constName_3371_, v___y_3372_, v___y_3373_);
    leanh::lean_dec(v___y_3373_);
    leanh::lean_dec_ref(v___y_3372_);
    return v_res_3375_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__1(
    mut v_a_3376_: *mut leanh::LeanObject,
    mut v_a_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3376_) == 0 {
                    v___x_3378_ = l_List_reverse___redArg(v_a_3377_);
                    return v___x_3378_;
                } else {
                    v_head_3379_ = leanh::lean_ctor_get(v_a_3376_, 0);
                    v_tail_3380_ = leanh::lean_ctor_get(v_a_3376_, 1);
                    v_isSharedCheck_3389_ = (!leanh::lean_is_exclusive(v_a_3376_)) as u8;
                    if v_isSharedCheck_3389_ == 0 {
                        v___x_3382_ = v_a_3376_;
                        v_isShared_3383_ = v_isSharedCheck_3389_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3380_);
                        leanh::lean_inc(v_head_3379_);
                        leanh::lean_dec(v_a_3376_);
                        v___x_3382_ = leanh::lean_box(0);
                        v_isShared_3383_ = v_isSharedCheck_3389_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3384_ = l_Lean_mkLevelParam(v_head_3379_);
                if v_isShared_3383_ == 0 {
                    leanh::lean_ctor_set(v___x_3382_, 1, v_a_3377_);
                    leanh::lean_ctor_set(v___x_3382_, 0, v___x_3384_);
                    v___x_3386_ = v___x_3382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_a_3377_);
                    v___x_3386_ = v_reuseFailAlloc_3388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3376_ = v_tail_3380_;
                v_a_3377_ = v___x_3386_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(
    mut v_constName_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v_levelParams_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3406_: u8 = 0;
    let mut v_a_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_constName_3390_);
                v___x_3394_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0(v_constName_3390_, v___y_3391_, v___y_3392_);
                if leanh::lean_obj_tag(v___x_3394_) == 0 {
                    v_a_3395_ = leanh::lean_ctor_get(v___x_3394_, 0);
                    v_isSharedCheck_3406_ = (!leanh::lean_is_exclusive(v___x_3394_)) as u8;
                    if v_isSharedCheck_3406_ == 0 {
                        v___x_3397_ = v___x_3394_;
                        v_isShared_3398_ = v_isSharedCheck_3406_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3395_);
                        leanh::lean_dec(v___x_3394_);
                        v___x_3397_ = leanh::lean_box(0);
                        v_isShared_3398_ = v_isSharedCheck_3406_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_constName_3390_);
                    v_a_3407_ = leanh::lean_ctor_get(v___x_3394_, 0);
                    v_isSharedCheck_3414_ = (!leanh::lean_is_exclusive(v___x_3394_)) as u8;
                    if v_isSharedCheck_3414_ == 0 {
                        v___x_3409_ = v___x_3394_;
                        v_isShared_3410_ = v_isSharedCheck_3414_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3407_);
                        leanh::lean_dec(v___x_3394_);
                        v___x_3409_ = leanh::lean_box(0);
                        v_isShared_3410_ = v_isSharedCheck_3414_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_3399_ = leanh::lean_ctor_get(v_a_3395_, 1);
                leanh::lean_inc(v_levelParams_3399_);
                leanh::lean_dec(v_a_3395_);
                v___x_3400_ = leanh::lean_box(0);
                v___x_3401_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__1(v_levelParams_3399_, v___x_3400_);
                v___x_3402_ = l_Lean_mkConst(v_constName_3390_, v___x_3401_);
                if v_isShared_3398_ == 0 {
                    leanh::lean_ctor_set(v___x_3397_, 0, v___x_3402_);
                    v___x_3404_ = v___x_3397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3402_);
                    v___x_3404_ = v_reuseFailAlloc_3405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3404_;
            }
            3 => {
                if v_isShared_3410_ == 0 {
                    v___x_3412_ = v___x_3409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
                    v___x_3412_ = v_reuseFailAlloc_3413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0___boxed(
    mut v_constName_3415_: *mut leanh::LeanObject,
    mut v___y_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3419_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(
        v_constName_3415_,
        v___y_3416_,
        v___y_3417_,
    );
    leanh::lean_dec(v___y_3417_);
    leanh::lean_dec_ref(v___y_3416_);
    return v_res_3419_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabImportPath___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3421_ = l_Lean_Elab_Command_elabImportPath___closed__0;
    v___x_3422_ = l_Lean_stringToMessageData(v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabImportPath___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = l_Lean_Elab_Command_elabImportPath___closed__2;
    v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
    return v___x_3425_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabImportPath___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3427_ = l_Lean_Elab_Command_elabImportPath___closed__4;
    v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
    return v___x_3428_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabImportPath___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3430_ = l_Lean_Elab_Command_elabImportPath___closed__6;
    v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
    return v___x_3431_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabImportPath___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_Elab_Command_elabImportPath___closed__8;
    v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
    return v___x_3434_;
}
pub unsafe fn l_Lean_Elab_Command_elabImportPath(
    mut v_stx_3435_: *mut leanh::LeanObject,
    mut v_a_3436_: *mut leanh::LeanObject,
    mut v_a_3437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3468_: u8 = 0;
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3472_: u8 = 0;
    let mut v_a_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3476_: u8 = 0;
    let mut v___x_3477_: u8 = 0;
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3487_: u8 = 0;
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v_unused_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3439_ = lean_st_ref_get(v_a_3437_);
                v___x_3440_ = leanh::lean_unsigned_to_nat(1);
                v_n_3441_ = l_Lean_Syntax_getArg(v_stx_3435_, v___x_3440_);
                v___x_3442_ = leanh::lean_box(0);
                leanh::lean_inc(v_n_3441_);
                v___x_3443_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___x_3443_, 0, v_n_3441_);
                leanh::lean_closure_set(v___x_3443_, 1, v___x_3442_);
                v___x_3444_ =
                    l_Lean_Elab_Command_liftCoreM___redArg(v___x_3443_, v_a_3436_, v_a_3437_);
                if leanh::lean_obj_tag(v___x_3444_) == 0 {
                    v_a_3445_ = leanh::lean_ctor_get(v___x_3444_, 0);
                    leanh::lean_inc_n(v_a_3445_, 2);
                    leanh::lean_dec_ref_known(v___x_3444_, 1);
                    v___x_3446_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(v_a_3445_, v_a_3436_, v_a_3437_);
                    if leanh::lean_obj_tag(v___x_3446_) == 0 {
                        v_a_3447_ = leanh::lean_ctor_get(v___x_3446_, 0);
                        leanh::lean_inc(v_a_3447_);
                        leanh::lean_dec_ref_known(v___x_3446_, 1);
                        v_env_3448_ = leanh::lean_ctor_get(v___x_3439_, 0);
                        leanh::lean_inc_ref(v_env_3448_);
                        leanh::lean_dec(v___x_3439_);
                        v___x_3449_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_3448_, v_a_3445_);
                        leanh::lean_dec(v_a_3445_);
                        if leanh::lean_obj_tag(v___x_3449_) == 1 {
                            v_val_3450_ = leanh::lean_ctor_get(v___x_3449_, 0);
                            leanh::lean_inc(v_val_3450_);
                            leanh::lean_dec_ref_known(v___x_3449_, 1);
                            v___x_3451_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__1_once
                                ),
                                _init_l_Lean_Elab_Command_elabImportPath___closed__1,
                            );
                            v___x_3452_ = l_Lean_MessageData_ofExpr(v_a_3447_);
                            v___x_3453_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3453_, 0, v___x_3451_);
                            leanh::lean_ctor_set(v___x_3453_, 1, v___x_3452_);
                            v___x_3454_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__3_once
                                ),
                                _init_l_Lean_Elab_Command_elabImportPath___closed__3,
                            );
                            v___x_3455_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3455_, 0, v___x_3453_);
                            leanh::lean_ctor_set(v___x_3455_, 1, v___x_3454_);
                            v___x_3456_ =
                                l_Lean_Elab_Command_importPathMessage(v_env_3448_, v_val_3450_);
                            leanh::lean_dec(v_val_3450_);
                            leanh::lean_dec_ref(v_env_3448_);
                            v___x_3457_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3457_, 0, v___x_3455_);
                            leanh::lean_ctor_set(v___x_3457_, 1, v___x_3456_);
                            v___x_3458_ =
                                l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(
                                    v_n_3441_,
                                    v___x_3457_,
                                    v_a_3436_,
                                    v_a_3437_,
                                );
                            leanh::lean_dec(v_n_3441_);
                            return v___x_3458_;
                        } else {
                            leanh::lean_dec(v___x_3449_);
                            leanh::lean_dec_ref(v_env_3448_);
                            v___x_3459_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__1_once
                                ),
                                _init_l_Lean_Elab_Command_elabImportPath___closed__1,
                            );
                            v___x_3460_ = l_Lean_MessageData_ofExpr(v_a_3447_);
                            v___x_3461_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3461_, 0, v___x_3459_);
                            leanh::lean_ctor_set(v___x_3461_, 1, v___x_3460_);
                            v___x_3462_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabImportPath___closed__5_once
                                ),
                                _init_l_Lean_Elab_Command_elabImportPath___closed__5,
                            );
                            v___x_3463_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3463_, 0, v___x_3461_);
                            leanh::lean_ctor_set(v___x_3463_, 1, v___x_3462_);
                            v___x_3464_ =
                                l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(
                                    v_n_3441_,
                                    v___x_3463_,
                                    v_a_3436_,
                                    v_a_3437_,
                                );
                            leanh::lean_dec(v_n_3441_);
                            return v___x_3464_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3445_);
                        leanh::lean_dec(v_n_3441_);
                        leanh::lean_dec(v___x_3439_);
                        v_a_3465_ = leanh::lean_ctor_get(v___x_3446_, 0);
                        v_isSharedCheck_3472_ =
                            (!leanh::lean_is_exclusive(v___x_3446_)) as u8;
                        if v_isSharedCheck_3472_ == 0 {
                            v___x_3467_ = v___x_3446_;
                            v_isShared_3468_ = v_isSharedCheck_3472_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3465_);
                            leanh::lean_dec(v___x_3446_);
                            v___x_3467_ = leanh::lean_box(0);
                            v_isShared_3468_ = v_isSharedCheck_3472_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3439_);
                    v_a_3473_ = leanh::lean_ctor_get(v___x_3444_, 0);
                    v_isSharedCheck_3497_ = (!leanh::lean_is_exclusive(v___x_3444_)) as u8;
                    if v_isSharedCheck_3497_ == 0 {
                        v___x_3475_ = v___x_3444_;
                        v_isShared_3476_ = v_isSharedCheck_3497_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3473_);
                        leanh::lean_dec(v___x_3444_);
                        v___x_3475_ = leanh::lean_box(0);
                        v_isShared_3476_ = v_isSharedCheck_3497_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3468_ == 0 {
                    v___x_3470_ = v___x_3467_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
                    v___x_3470_ = v_reuseFailAlloc_3471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3470_;
            }
            3 => {
                v___x_3477_ = l_Lean_Exception_isInterrupt(v_a_3473_);
                if v___x_3477_ == 0 {
                    leanh::lean_del_object(v___x_3475_);
                    leanh::lean_dec(v_a_3473_);
                    v___x_3478_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabImportPath___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabImportPath___closed__7_once
                        ),
                        _init_l_Lean_Elab_Command_elabImportPath___closed__7,
                    );
                    v___x_3479_ = l_Lean_Syntax_getId(v_n_3441_);
                    v___x_3480_ = l_Lean_MessageData_ofName(v___x_3479_);
                    v___x_3481_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3481_, 0, v___x_3478_);
                    leanh::lean_ctor_set(v___x_3481_, 1, v___x_3480_);
                    v___x_3482_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabImportPath___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabImportPath___closed__9_once
                        ),
                        _init_l_Lean_Elab_Command_elabImportPath___closed__9,
                    );
                    v___x_3483_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3483_, 0, v___x_3481_);
                    leanh::lean_ctor_set(v___x_3483_, 1, v___x_3482_);
                    v___x_3484_ =
                        l_Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1(
                            v_n_3441_,
                            v___x_3483_,
                            v_a_3436_,
                            v_a_3437_,
                        );
                    leanh::lean_dec(v_n_3441_);
                    if leanh::lean_obj_tag(v___x_3484_) == 0 {
                        v_isSharedCheck_3492_ =
                            (!leanh::lean_is_exclusive(v___x_3484_)) as u8;
                        if v_isSharedCheck_3492_ == 0 {
                            v_unused_3493_ = leanh::lean_ctor_get(v___x_3484_, 0);
                            leanh::lean_dec(v_unused_3493_);
                            v___x_3486_ = v___x_3484_;
                            v_isShared_3487_ = v_isSharedCheck_3492_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3484_);
                            v___x_3486_ = leanh::lean_box(0);
                            v_isShared_3487_ = v_isSharedCheck_3492_;
                            state = 4;
                            continue;
                        }
                    } else {
                        return v___x_3484_;
                    }
                } else {
                    leanh::lean_dec(v_n_3441_);
                    if v_isShared_3476_ == 0 {
                        v___x_3495_ = v___x_3475_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3496_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3473_);
                        v___x_3495_ = v_reuseFailAlloc_3496_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3488_ = leanh::lean_box(0);
                if v_isShared_3487_ == 0 {
                    leanh::lean_ctor_set(v___x_3486_, 0, v___x_3488_);
                    v___x_3490_ = v___x_3486_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
                    v___x_3490_ = v_reuseFailAlloc_3491_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3490_;
            }
            6 => {
                return v___x_3495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabImportPath___boxed(
    mut v_stx_3498_: *mut leanh::LeanObject,
    mut v_a_3499_: *mut leanh::LeanObject,
    mut v_a_3500_: *mut leanh::LeanObject,
    mut v_a_3501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3502_ = l_Lean_Elab_Command_elabImportPath(v_stx_3498_, v_a_3499_, v_a_3500_);
    leanh::lean_dec(v_a_3500_);
    leanh::lean_dec_ref(v_a_3499_);
    leanh::lean_dec(v_stx_3498_);
    return v_res_3502_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5(
    mut v_msgData_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3507_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___redArg(v_msgData_3503_, v___y_3505_);
    return v___x_3507_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5___boxed(
    mut v_msgData_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3_spec__5(v_msgData_3508_, v___y_3509_, v___y_3510_);
    leanh::lean_dec(v___y_3510_);
    leanh::lean_dec_ref(v___y_3509_);
    return v_res_3512_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3513_: *mut leanh::LeanObject,
    mut v_constName_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
    mut v___y_3516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3518_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___redArg(v_constName_3514_, v___y_3515_, v___y_3516_);
    return v___x_3518_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3519_: *mut leanh::LeanObject,
    mut v_constName_3520_: *mut leanh::LeanObject,
    mut v___y_3521_: *mut leanh::LeanObject,
    mut v___y_3522_: *mut leanh::LeanObject,
    mut v___y_3523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3524_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1(v_00_u03b1_3519_, v_constName_3520_, v___y_3521_, v___y_3522_);
    leanh::lean_dec(v___y_3522_);
    leanh::lean_dec_ref(v___y_3521_);
    return v_res_3524_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_3525_: *mut leanh::LeanObject,
    mut v_ref_3526_: *mut leanh::LeanObject,
    mut v_constName_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3526_, v_constName_3527_, v___y_3528_, v___y_3529_);
    return v___x_3531_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_3532_: *mut leanh::LeanObject,
    mut v_ref_3533_: *mut leanh::LeanObject,
    mut v_constName_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3538_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_3532_, v_ref_3533_, v_constName_3534_, v___y_3535_, v___y_3536_);
    leanh::lean_dec(v___y_3536_);
    leanh::lean_dec_ref(v___y_3535_);
    leanh::lean_dec(v_ref_3533_);
    return v_res_3538_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8(
    mut v_00_u03b1_3539_: *mut leanh::LeanObject,
    mut v_ref_3540_: *mut leanh::LeanObject,
    mut v_msg_3541_: *mut leanh::LeanObject,
    mut v_declHint_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_3540_, v_msg_3541_, v_declHint_3542_, v___y_3543_, v___y_3544_);
    return v___x_3546_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b1_3547_: *mut leanh::LeanObject,
    mut v_ref_3548_: *mut leanh::LeanObject,
    mut v_msg_3549_: *mut leanh::LeanObject,
    mut v_declHint_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3554_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b1_3547_, v_ref_3548_, v_msg_3549_, v_declHint_3550_, v___y_3551_, v___y_3552_);
    leanh::lean_dec(v___y_3552_);
    leanh::lean_dec_ref(v___y_3551_);
    leanh::lean_dec(v_ref_3548_);
    return v_res_3554_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10(
    mut v_msg_3555_: *mut leanh::LeanObject,
    mut v_declHint_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3560_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___redArg(v_msg_3555_, v_declHint_3556_, v___y_3558_);
    return v___x_3560_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10___boxed(
    mut v_msg_3561_: *mut leanh::LeanObject,
    mut v_declHint_3562_: *mut leanh::LeanObject,
    mut v___y_3563_: *mut leanh::LeanObject,
    mut v___y_3564_: *mut leanh::LeanObject,
    mut v___y_3565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3566_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__9_spec__10(v_msg_3561_, v_declHint_3562_, v___y_3563_, v___y_3564_);
    leanh::lean_dec(v___y_3564_);
    leanh::lean_dec_ref(v___y_3563_);
    return v_res_3566_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10(
    mut v_00_u03b1_3567_: *mut leanh::LeanObject,
    mut v_ref_3568_: *mut leanh::LeanObject,
    mut v_msg_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3573_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___redArg(v_ref_3568_, v_msg_3569_, v___y_3570_, v___y_3571_);
    return v___x_3573_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10___boxed(
    mut v_00_u03b1_3574_: *mut leanh::LeanObject,
    mut v_ref_3575_: *mut leanh::LeanObject,
    mut v_msg_3576_: *mut leanh::LeanObject,
    mut v___y_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3580_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10(v_00_u03b1_3574_, v_ref_3575_, v_msg_3576_, v___y_3577_, v___y_3578_);
    leanh::lean_dec(v___y_3578_);
    leanh::lean_dec_ref(v___y_3577_);
    leanh::lean_dec(v_ref_3575_);
    return v_res_3580_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12(
    mut v_00_u03b1_3581_: *mut leanh::LeanObject,
    mut v_msg_3582_: *mut leanh::LeanObject,
    mut v___y_3583_: *mut leanh::LeanObject,
    mut v___y_3584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___redArg(v_msg_3582_, v___y_3583_, v___y_3584_);
    return v___x_3586_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12___boxed(
    mut v_00_u03b1_3587_: *mut leanh::LeanObject,
    mut v_msg_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
    mut v___y_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3592_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12(v_00_u03b1_3587_, v_msg_3588_, v___y_3589_, v___y_3590_);
    leanh::lean_dec(v___y_3590_);
    leanh::lean_dec_ref(v___y_3589_);
    return v_res_3592_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13(
    mut v_msgData_3593_: *mut leanh::LeanObject,
    mut v_macroStack_3594_: *mut leanh::LeanObject,
    mut v___y_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___redArg(v_msgData_3593_, v_macroStack_3594_, v___y_3596_);
    return v___x_3598_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13___boxed(
    mut v_msgData_3599_: *mut leanh::LeanObject,
    mut v_macroStack_3600_: *mut leanh::LeanObject,
    mut v___y_3601_: *mut leanh::LeanObject,
    mut v___y_3602_: *mut leanh::LeanObject,
    mut v___y_3603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3604_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0_spec__0_spec__1_spec__3_spec__8_spec__10_spec__12_spec__13(v_msgData_3599_, v_macroStack_3600_, v___y_3601_, v___y_3602_);
    leanh::lean_dec(v___y_3602_);
    leanh::lean_dec_ref(v___y_3601_);
    return v_res_3604_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1()
-> *mut leanh::LeanObject {
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3619_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3620_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__2;
    v___x_3621_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4;
    v___x_3622_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabImportPath___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3623_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3619_,
        v___x_3620_,
        v___x_3621_,
        v___x_3622_,
    );
    return v___x_3623_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___boxed(
    mut v_a_3624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3625_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1();
    return v_res_3625_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3()
-> *mut leanh::LeanObject {
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1___closed__4;
    v___x_3629_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___closed__0;
    v___x_3630_ = l_Lean_addBuiltinDocString(v___x_3628_, v___x_3629_);
    return v___x_3630_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3___boxed(
    mut v_a_3631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3632_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3();
    return v_res_3632_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(
    mut v___y_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3635_ = lean_st_ref_get(v___y_3633_);
    v_env_3636_ = leanh::lean_ctor_get(v___x_3635_, 0);
    leanh::lean_inc_ref(v_env_3636_);
    leanh::lean_dec(v___x_3635_);
    v___x_3637_ = l_Lean_Environment_header(v_env_3636_);
    leanh::lean_dec_ref(v_env_3636_);
    v_mainModule_3638_ = leanh::lean_ctor_get(v___x_3637_, 0);
    leanh::lean_inc(v_mainModule_3638_);
    leanh::lean_dec_ref(v___x_3637_);
    v___x_3639_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3639_, 0, v_mainModule_3638_);
    return v___x_3639_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg___boxed(
    mut v___y_3640_: *mut leanh::LeanObject,
    mut v___y_3641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3642_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(
            v___y_3640_,
        );
    leanh::lean_dec(v___y_3640_);
    return v_res_3642_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1(
    mut v___y_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3646_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(
            v___y_3644_,
        );
    return v___x_3646_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___boxed(
    mut v___y_3647_: *mut leanh::LeanObject,
    mut v___y_3648_: *mut leanh::LeanObject,
    mut v___y_3649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1(
        v___y_3647_,
        v___y_3648_,
    );
    leanh::lean_dec(v___y_3648_);
    leanh::lean_dec_ref(v___y_3647_);
    return v_res_3650_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0(
    mut v_ref_3651_: *mut leanh::LeanObject,
    mut v_msgData_3652_: *mut leanh::LeanObject,
    mut v___y_3653_: *mut leanh::LeanObject,
    mut v___y_3654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3656_: u8 = 0;
    let mut v___x_3657_: u8 = 0;
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3656_ = 2;
    v___x_3657_ = 0;
    v___x_3658_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_3651_, v_msgData_3652_, v___x_3656_, v___x_3657_, v___y_3653_, v___y_3654_);
    return v___x_3658_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0___boxed(
    mut v_ref_3659_: *mut leanh::LeanObject,
    mut v_msgData_3660_: *mut leanh::LeanObject,
    mut v___y_3661_: *mut leanh::LeanObject,
    mut v___y_3662_: *mut leanh::LeanObject,
    mut v___y_3663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3664_ = l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0(
        v_ref_3659_,
        v_msgData_3660_,
        v___y_3661_,
        v___y_3662_,
    );
    leanh::lean_dec(v___y_3662_);
    leanh::lean_dec_ref(v___y_3661_);
    leanh::lean_dec(v_ref_3659_);
    return v_res_3664_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__0;
    v___x_3667_ = l_Lean_stringToMessageData(v___x_3666_);
    return v___x_3667_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__2;
    v___x_3670_ = l_Lean_stringToMessageData(v___x_3669_);
    return v___x_3670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2(
    mut v___x_3671_: *mut leanh::LeanObject,
    mut v_as_3672_: *mut leanh::LeanObject,
    mut v_sz_3673_: usize,
    mut v_i_3674_: usize,
    mut v_b_3675_: *mut leanh::LeanObject,
    mut v___y_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: usize = 0;
    let mut v___x_3682_: usize = 0;
    let mut v___x_3684_: u8 = 0;
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3716_: u8 = 0;
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_a_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3725_: u8 = 0;
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3733_: u8 = 0;
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3737_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3684_ = lean_usize_dec_lt(v_i_3674_, v_sz_3673_);
                if v___x_3684_ == 0 {
                    v___x_3685_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3685_, 0, v_b_3675_);
                    return v___x_3685_;
                } else {
                    v___x_3686_ = leanh::lean_box(0);
                    v_a_3687_ = lean_array_uget_borrowed(v_as_3672_, v_i_3674_);
                    v___x_3688_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_3687_);
                    v___x_3689_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed
                            as *mut core::ffi::c_void,
                        5,
                        2,
                    );
                    leanh::lean_closure_set(v___x_3689_, 0, v_a_3687_);
                    leanh::lean_closure_set(v___x_3689_, 1, v___x_3688_);
                    v___x_3690_ = l_Lean_Elab_Command_liftCoreM___redArg(
                        v___x_3689_,
                        v___y_3676_,
                        v___y_3677_,
                    );
                    if leanh::lean_obj_tag(v___x_3690_) == 0 {
                        v_a_3691_ = leanh::lean_ctor_get(v___x_3690_, 0);
                        leanh::lean_inc_n(v_a_3691_, 2);
                        leanh::lean_dec_ref_known(v___x_3690_, 1);
                        v___x_3692_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_Command_elabImportPath_spec__0(v_a_3691_, v___y_3676_, v___y_3677_);
                        if leanh::lean_obj_tag(v___x_3692_) == 0 {
                            v_a_3693_ = leanh::lean_ctor_get(v___x_3692_, 0);
                            leanh::lean_inc(v_a_3693_);
                            leanh::lean_dec_ref_known(v___x_3692_, 1);
                            v___x_3699_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v___x_3671_, v_a_3691_);
                            leanh::lean_dec(v_a_3691_);
                            if leanh::lean_obj_tag(v___x_3699_) == 1 {
                                v_val_3700_ = leanh::lean_ctor_get(v___x_3699_, 0);
                                leanh::lean_inc(v_val_3700_);
                                leanh::lean_dec_ref_known(v___x_3699_, 1);
                                v___x_3701_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Command_elabImportPath___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Command_elabImportPath___closed__1_once
                                    ),
                                    _init_l_Lean_Elab_Command_elabImportPath___closed__1,
                                );
                                v___x_3702_ = l_Lean_MessageData_ofExpr(v_a_3693_);
                                v___x_3703_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3703_, 0, v___x_3701_);
                                leanh::lean_ctor_set(v___x_3703_, 1, v___x_3702_);
                                v___x_3704_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__3);
                                v___x_3705_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3705_, 0, v___x_3703_);
                                leanh::lean_ctor_set(v___x_3705_, 1, v___x_3704_);
                                v___x_3706_ =
                                    l_Lean_Elab_Command_importPathMessage(v___x_3671_, v_val_3700_);
                                leanh::lean_dec(v_val_3700_);
                                v___x_3707_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3707_, 0, v___x_3705_);
                                leanh::lean_ctor_set(v___x_3707_, 1, v___x_3706_);
                                v_a_3695_ = v___x_3707_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3699_);
                                v___x_3708_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Command_elabImportPath___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Command_elabImportPath___closed__1_once
                                    ),
                                    _init_l_Lean_Elab_Command_elabImportPath___closed__1,
                                );
                                v___x_3709_ = l_Lean_MessageData_ofExpr(v_a_3693_);
                                v___x_3710_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3710_, 0, v___x_3708_);
                                leanh::lean_ctor_set(v___x_3710_, 1, v___x_3709_);
                                v___x_3711_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Command_elabImportPath___closed__5
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Command_elabImportPath___closed__5_once
                                    ),
                                    _init_l_Lean_Elab_Command_elabImportPath___closed__5,
                                );
                                v___x_3712_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3712_, 0, v___x_3710_);
                                leanh::lean_ctor_set(v___x_3712_, 1, v___x_3711_);
                                v_a_3695_ = v___x_3712_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3691_);
                            v_a_3713_ = leanh::lean_ctor_get(v___x_3692_, 0);
                            v_isSharedCheck_3720_ =
                                (!leanh::lean_is_exclusive(v___x_3692_)) as u8;
                            if v_isSharedCheck_3720_ == 0 {
                                v___x_3715_ = v___x_3692_;
                                v_isShared_3716_ = v_isSharedCheck_3720_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3713_);
                                leanh::lean_dec(v___x_3692_);
                                v___x_3715_ = leanh::lean_box(0);
                                v_isShared_3716_ = v_isSharedCheck_3720_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_3721_ = leanh::lean_ctor_get(v___x_3690_, 0);
                        v_isSharedCheck_3741_ =
                            (!leanh::lean_is_exclusive(v___x_3690_)) as u8;
                        if v_isSharedCheck_3741_ == 0 {
                            v___x_3723_ = v___x_3690_;
                            v_isShared_3724_ = v_isSharedCheck_3741_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3721_);
                            leanh::lean_dec(v___x_3690_);
                            v___x_3723_ = leanh::lean_box(0);
                            v_isShared_3724_ = v_isSharedCheck_3741_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3681_ = 1usize;
                v___x_3682_ = lean_usize_add(v_i_3674_, v___x_3681_);
                v_i_3674_ = v___x_3682_;
                v_b_3675_ = v_a_3680_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___closed__1);
                v___x_3697_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3697_, 0, v_a_3695_);
                leanh::lean_ctor_set(v___x_3697_, 1, v___x_3696_);
                v___x_3698_ =
                    l_Lean_logErrorAt___at___00Lean_Elab_Command_elabAssertNotExists_spec__0(
                        v_a_3687_,
                        v___x_3697_,
                        v___y_3676_,
                        v___y_3677_,
                    );
                if leanh::lean_obj_tag(v___x_3698_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3698_, 1);
                    v_a_3680_ = v___x_3686_;
                    state = 1;
                    continue;
                } else {
                    return v___x_3698_;
                }
            }
            3 => {
                if v_isShared_3716_ == 0 {
                    v___x_3718_ = v___x_3715_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
                    v___x_3718_ = v_reuseFailAlloc_3719_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3718_;
            }
            5 => {
                v___x_3725_ = l_Lean_Exception_isInterrupt(v_a_3721_);
                if v___x_3725_ == 0 {
                    leanh::lean_del_object(v___x_3723_);
                    leanh::lean_dec(v_a_3721_);
                    v___x_3726_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(v___y_3677_);
                    if leanh::lean_obj_tag(v___x_3726_) == 0 {
                        v_a_3727_ = leanh::lean_ctor_get(v___x_3726_, 0);
                        leanh::lean_inc(v_a_3727_);
                        leanh::lean_dec_ref_known(v___x_3726_, 1);
                        v___x_3728_ = l_Lean_Syntax_getId(v_a_3687_);
                        v___x_3729_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(
                            v___x_3684_,
                            v___x_3728_,
                            v_a_3727_,
                            v___y_3677_,
                        );
                        if leanh::lean_obj_tag(v___x_3729_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3729_, 1);
                            v_a_3680_ = v___x_3686_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_3729_;
                        }
                    } else {
                        v_a_3730_ = leanh::lean_ctor_get(v___x_3726_, 0);
                        v_isSharedCheck_3737_ =
                            (!leanh::lean_is_exclusive(v___x_3726_)) as u8;
                        if v_isSharedCheck_3737_ == 0 {
                            v___x_3732_ = v___x_3726_;
                            v_isShared_3733_ = v_isSharedCheck_3737_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3730_);
                            leanh::lean_dec(v___x_3726_);
                            v___x_3732_ = leanh::lean_box(0);
                            v_isShared_3733_ = v_isSharedCheck_3737_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_3724_ == 0 {
                        v___x_3739_ = v___x_3723_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3721_);
                        v___x_3739_ = v_reuseFailAlloc_3740_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3733_ == 0 {
                    v___x_3735_ = v___x_3732_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3736_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
                    v___x_3735_ = v_reuseFailAlloc_3736_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3735_;
            }
            8 => {
                return v___x_3739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2___boxed(
    mut v___x_3742_: *mut leanh::LeanObject,
    mut v_as_3743_: *mut leanh::LeanObject,
    mut v_sz_3744_: *mut leanh::LeanObject,
    mut v_i_3745_: *mut leanh::LeanObject,
    mut v_b_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3750_: usize = 0;
    let mut v_i_boxed_3751_: usize = 0;
    let mut v_res_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3750_ = leanh::lean_unbox_usize(v_sz_3744_);
    leanh::lean_dec(v_sz_3744_);
    v_i_boxed_3751_ = leanh::lean_unbox_usize(v_i_3745_);
    leanh::lean_dec(v_i_3745_);
    v_res_3752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2(v___x_3742_, v_as_3743_, v_sz_boxed_3750_, v_i_boxed_3751_, v_b_3746_, v___y_3747_, v___y_3748_);
    leanh::lean_dec(v___y_3748_);
    leanh::lean_dec_ref(v___y_3747_);
    leanh::lean_dec_ref(v_as_3743_);
    leanh::lean_dec_ref(v___x_3742_);
    return v_res_3752_;
}
pub unsafe fn l_Lean_Elab_Command_elabAssertNotExists(
    mut v_stx_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
    mut v_a_3755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3763_: usize = 0;
    let mut v___x_3764_: usize = 0;
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3768_: u8 = 0;
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3772_: u8 = 0;
    let mut v_unused_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3757_ = lean_st_ref_get(v_a_3755_);
                v_env_3758_ = leanh::lean_ctor_get(v___x_3757_, 0);
                leanh::lean_inc_ref(v_env_3758_);
                leanh::lean_dec(v___x_3757_);
                v___x_3759_ = leanh::lean_unsigned_to_nat(1);
                v___x_3760_ = l_Lean_Syntax_getArg(v_stx_3753_, v___x_3759_);
                v___x_3761_ = l_Lean_Syntax_getArgs(v___x_3760_);
                leanh::lean_dec(v___x_3760_);
                v___x_3762_ = leanh::lean_box(0);
                v_sz_3763_ = lean_array_size(v___x_3761_);
                v___x_3764_ = 0usize;
                v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotExists_spec__2(v_env_3758_, v___x_3761_, v_sz_3763_, v___x_3764_, v___x_3762_, v_a_3754_, v_a_3755_);
                leanh::lean_dec_ref(v___x_3761_);
                leanh::lean_dec_ref(v_env_3758_);
                if leanh::lean_obj_tag(v___x_3765_) == 0 {
                    v_isSharedCheck_3772_ = (!leanh::lean_is_exclusive(v___x_3765_)) as u8;
                    if v_isSharedCheck_3772_ == 0 {
                        v_unused_3773_ = leanh::lean_ctor_get(v___x_3765_, 0);
                        leanh::lean_dec(v_unused_3773_);
                        v___x_3767_ = v___x_3765_;
                        v_isShared_3768_ = v_isSharedCheck_3772_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3765_);
                        v___x_3767_ = leanh::lean_box(0);
                        v_isShared_3768_ = v_isSharedCheck_3772_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3765_;
                }
            }
            1 => {
                if v_isShared_3768_ == 0 {
                    leanh::lean_ctor_set(v___x_3767_, 0, v___x_3762_);
                    v___x_3770_ = v___x_3767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3762_);
                    v___x_3770_ = v_reuseFailAlloc_3771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabAssertNotExists___boxed(
    mut v_stx_3774_: *mut leanh::LeanObject,
    mut v_a_3775_: *mut leanh::LeanObject,
    mut v_a_3776_: *mut leanh::LeanObject,
    mut v_a_3777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3778_ = l_Lean_Elab_Command_elabAssertNotExists(v_stx_3774_, v_a_3775_, v_a_3776_);
    leanh::lean_dec(v_a_3776_);
    leanh::lean_dec_ref(v_a_3775_);
    leanh::lean_dec(v_stx_3774_);
    return v_res_3778_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1()
-> *mut leanh::LeanObject {
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3792_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3793_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__1;
    v___x_3794_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3;
    v___x_3795_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabAssertNotExists___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3796_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3792_,
        v___x_3793_,
        v___x_3794_,
        v___x_3795_,
    );
    return v___x_3796_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___boxed(
    mut v_a_3797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3798_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1();
    return v_res_3798_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3()
-> *mut leanh::LeanObject {
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3801_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1___closed__3;
    v___x_3802_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___closed__0;
    v___x_3803_ = l_Lean_addBuiltinDocString(v___x_3801_, v___x_3802_);
    return v___x_3803_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3___boxed(
    mut v_a_3804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3805_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3();
    return v_res_3805_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0(
    mut v_ref_3806_: *mut leanh::LeanObject,
    mut v_msgData_3807_: *mut leanh::LeanObject,
    mut v___y_3808_: *mut leanh::LeanObject,
    mut v___y_3809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3811_ = 1;
    v___x_3812_ = 0;
    v___x_3813_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_ref_3806_, v_msgData_3807_, v___x_3811_, v___x_3812_, v___y_3808_, v___y_3809_);
    return v___x_3813_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0___boxed(
    mut v_ref_3814_: *mut leanh::LeanObject,
    mut v_msgData_3815_: *mut leanh::LeanObject,
    mut v___y_3816_: *mut leanh::LeanObject,
    mut v___y_3817_: *mut leanh::LeanObject,
    mut v___y_3818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3819_ = l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0(
        v_ref_3814_,
        v_msgData_3815_,
        v___y_3816_,
        v___y_3817_,
    );
    leanh::lean_dec(v___y_3817_);
    leanh::lean_dec_ref(v___y_3816_);
    leanh::lean_dec(v_ref_3814_);
    return v_res_3819_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__0;
    v___x_3822_ = l_Lean_stringToMessageData(v___x_3821_);
    return v___x_3822_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__2;
    v___x_3825_ = l_Lean_stringToMessageData(v___x_3824_);
    return v___x_3825_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1(
    mut v___x_3826_: *mut leanh::LeanObject,
    mut v_as_3827_: *mut leanh::LeanObject,
    mut v_sz_3828_: usize,
    mut v_i_3829_: usize,
    mut v_b_3830_: *mut leanh::LeanObject,
    mut v___y_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: usize = 0;
    let mut v___x_3837_: usize = 0;
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: u8 = 0;
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3839_ = lean_usize_dec_lt(v_i_3829_, v_sz_3828_);
                if v___x_3839_ == 0 {
                    v___x_3840_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3840_, 0, v_b_3830_);
                    return v___x_3840_;
                } else {
                    v___x_3841_ = leanh::lean_box(0);
                    v_a_3842_ = lean_array_uget_borrowed(v_as_3827_, v_i_3829_);
                    v___x_3843_ = l_Lean_Syntax_getId(v_a_3842_);
                    v___x_3844_ = l_Lean_Environment_getModuleIdx_x3f(v___x_3826_, v___x_3843_);
                    if leanh::lean_obj_tag(v___x_3844_) == 1 {
                        leanh::lean_dec(v___x_3843_);
                        v_val_3845_ = leanh::lean_ctor_get(v___x_3844_, 0);
                        leanh::lean_inc(v_val_3845_);
                        leanh::lean_dec_ref_known(v___x_3844_, 1);
                        v___x_3846_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__1);
                        leanh::lean_inc(v_a_3842_);
                        v___x_3847_ = l_Lean_MessageData_ofSyntax(v_a_3842_);
                        v___x_3848_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3848_, 0, v___x_3846_);
                        leanh::lean_ctor_set(v___x_3848_, 1, v___x_3847_);
                        v___x_3849_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___closed__3);
                        v___x_3850_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3850_, 0, v___x_3848_);
                        leanh::lean_ctor_set(v___x_3850_, 1, v___x_3849_);
                        v___x_3851_ =
                            l_Lean_Elab_Command_importPathMessage(v___x_3826_, v_val_3845_);
                        leanh::lean_dec(v_val_3845_);
                        v___x_3852_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3852_, 0, v___x_3850_);
                        leanh::lean_ctor_set(v___x_3852_, 1, v___x_3851_);
                        v___x_3853_ = l_Lean_logWarningAt___at___00Lean_Elab_Command_elabAssertNotImported_spec__0(v_a_3842_, v___x_3852_, v___y_3831_, v___y_3832_);
                        if leanh::lean_obj_tag(v___x_3853_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3853_, 1);
                            v_a_3835_ = v___x_3841_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_3853_;
                        }
                    } else {
                        leanh::lean_dec(v___x_3844_);
                        v___x_3854_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabAssertNotExists_spec__1___redArg(v___y_3832_);
                        if leanh::lean_obj_tag(v___x_3854_) == 0 {
                            v_a_3855_ = leanh::lean_ctor_get(v___x_3854_, 0);
                            leanh::lean_inc(v_a_3855_);
                            leanh::lean_dec_ref_known(v___x_3854_, 1);
                            v___x_3856_ = 0;
                            v___x_3857_ = l_Lean_Elab_Command_addAssertExistsEntry___redArg(
                                v___x_3856_,
                                v___x_3843_,
                                v_a_3855_,
                                v___y_3832_,
                            );
                            if leanh::lean_obj_tag(v___x_3857_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3857_, 1);
                                v_a_3835_ = v___x_3841_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_3857_;
                            }
                        } else {
                            leanh::lean_dec(v___x_3843_);
                            v_a_3858_ = leanh::lean_ctor_get(v___x_3854_, 0);
                            v_isSharedCheck_3865_ =
                                (!leanh::lean_is_exclusive(v___x_3854_)) as u8;
                            if v_isSharedCheck_3865_ == 0 {
                                v___x_3860_ = v___x_3854_;
                                v_isShared_3861_ = v_isSharedCheck_3865_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3858_);
                                leanh::lean_dec(v___x_3854_);
                                v___x_3860_ = leanh::lean_box(0);
                                v_isShared_3861_ = v_isSharedCheck_3865_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3836_ = 1usize;
                v___x_3837_ = lean_usize_add(v_i_3829_, v___x_3836_);
                v_i_3829_ = v___x_3837_;
                v_b_3830_ = v_a_3835_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3861_ == 0 {
                    v___x_3863_ = v___x_3860_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
                    v___x_3863_ = v_reuseFailAlloc_3864_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1___boxed(
    mut v___x_3866_: *mut leanh::LeanObject,
    mut v_as_3867_: *mut leanh::LeanObject,
    mut v_sz_3868_: *mut leanh::LeanObject,
    mut v_i_3869_: *mut leanh::LeanObject,
    mut v_b_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3874_: usize = 0;
    let mut v_i_boxed_3875_: usize = 0;
    let mut v_res_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3874_ = leanh::lean_unbox_usize(v_sz_3868_);
    leanh::lean_dec(v_sz_3868_);
    v_i_boxed_3875_ = leanh::lean_unbox_usize(v_i_3869_);
    leanh::lean_dec(v_i_3869_);
    v_res_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1(v___x_3866_, v_as_3867_, v_sz_boxed_3874_, v_i_boxed_3875_, v_b_3870_, v___y_3871_, v___y_3872_);
    leanh::lean_dec(v___y_3872_);
    leanh::lean_dec_ref(v___y_3871_);
    leanh::lean_dec_ref(v_as_3867_);
    leanh::lean_dec_ref(v___x_3866_);
    return v_res_3876_;
}
pub unsafe fn l_Lean_Elab_Command_elabAssertNotImported(
    mut v_stx_3877_: *mut leanh::LeanObject,
    mut v_a_3878_: *mut leanh::LeanObject,
    mut v_a_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3887_: usize = 0;
    let mut v___x_3888_: usize = 0;
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_unused_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3881_ = lean_st_ref_get(v_a_3879_);
                v_env_3882_ = leanh::lean_ctor_get(v___x_3881_, 0);
                leanh::lean_inc_ref(v_env_3882_);
                leanh::lean_dec(v___x_3881_);
                v___x_3883_ = leanh::lean_unsigned_to_nat(1);
                v___x_3884_ = l_Lean_Syntax_getArg(v_stx_3877_, v___x_3883_);
                v___x_3885_ = l_Lean_Syntax_getArgs(v___x_3884_);
                leanh::lean_dec(v___x_3884_);
                v___x_3886_ = leanh::lean_box(0);
                v_sz_3887_ = lean_array_size(v___x_3885_);
                v___x_3888_ = 0usize;
                v___x_3889_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabAssertNotImported_spec__1(v_env_3882_, v___x_3885_, v_sz_3887_, v___x_3888_, v___x_3886_, v_a_3878_, v_a_3879_);
                leanh::lean_dec_ref(v___x_3885_);
                leanh::lean_dec_ref(v_env_3882_);
                if leanh::lean_obj_tag(v___x_3889_) == 0 {
                    v_isSharedCheck_3896_ = (!leanh::lean_is_exclusive(v___x_3889_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v_unused_3897_ = leanh::lean_ctor_get(v___x_3889_, 0);
                        leanh::lean_dec(v_unused_3897_);
                        v___x_3891_ = v___x_3889_;
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3889_);
                        v___x_3891_ = leanh::lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3889_;
                }
            }
            1 => {
                if v_isShared_3892_ == 0 {
                    leanh::lean_ctor_set(v___x_3891_, 0, v___x_3886_);
                    v___x_3894_ = v___x_3891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3886_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabAssertNotImported___boxed(
    mut v_stx_3898_: *mut leanh::LeanObject,
    mut v_a_3899_: *mut leanh::LeanObject,
    mut v_a_3900_: *mut leanh::LeanObject,
    mut v_a_3901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3902_ = l_Lean_Elab_Command_elabAssertNotImported(v_stx_3898_, v_a_3899_, v_a_3900_);
    leanh::lean_dec(v_a_3900_);
    leanh::lean_dec_ref(v_a_3899_);
    leanh::lean_dec(v_stx_3898_);
    return v_res_3902_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1()
-> *mut leanh::LeanObject {
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3916_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3917_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__1;
    v___x_3918_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3;
    v___x_3919_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabAssertNotImported___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3920_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3916_,
        v___x_3917_,
        v___x_3918_,
        v___x_3919_,
    );
    return v___x_3920_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___boxed(
    mut v_a_3921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3922_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1();
    return v_res_3922_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3()
-> *mut leanh::LeanObject {
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3925_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1___closed__3;
    v___x_3926_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___closed__0;
    v___x_3927_ = l_Lean_addBuiltinDocString(v___x_3925_, v___x_3926_);
    return v___x_3927_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3___boxed(
    mut v_a_3928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3();
    return v_res_3929_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(
    mut v_msgData_3930_: *mut leanh::LeanObject,
    mut v_severity_3931_: u8,
    mut v_isSilent_3932_: u8,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3936_ = l_Lean_Elab_Command_getRef___redArg(v___y_3933_);
                if leanh::lean_obj_tag(v___x_3936_) == 0 {
                    v_a_3937_ = leanh::lean_ctor_get(v___x_3936_, 0);
                    leanh::lean_inc(v_a_3937_);
                    leanh::lean_dec_ref_known(v___x_3936_, 1);
                    v___x_3938_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3(v_a_3937_, v_msgData_3930_, v_severity_3931_, v_isSilent_3932_, v___y_3933_, v___y_3934_);
                    leanh::lean_dec(v_a_3937_);
                    return v___x_3938_;
                } else {
                    leanh::lean_dec_ref(v_msgData_3930_);
                    v_a_3939_ = leanh::lean_ctor_get(v___x_3936_, 0);
                    v_isSharedCheck_3946_ = (!leanh::lean_is_exclusive(v___x_3936_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3941_ = v___x_3936_;
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3939_);
                        leanh::lean_dec(v___x_3936_);
                        v___x_3941_ = leanh::lean_box(0);
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3942_ == 0 {
                    v___x_3944_ = v___x_3941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
                    v___x_3944_ = v_reuseFailAlloc_3945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3___boxed(
    mut v_msgData_3947_: *mut leanh::LeanObject,
    mut v_severity_3948_: *mut leanh::LeanObject,
    mut v_isSilent_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_3953_: u8 = 0;
    let mut v_isSilent_boxed_3954_: u8 = 0;
    let mut v_res_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3953_ = (leanh::lean_unbox(v_severity_3948_) as u8);
    v_isSilent_boxed_3954_ = (leanh::lean_unbox(v_isSilent_3949_) as u8);
    v_res_3955_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(v_msgData_3947_, v_severity_boxed_3953_, v_isSilent_boxed_3954_, v___y_3950_, v___y_3951_);
    leanh::lean_dec(v___y_3951_);
    leanh::lean_dec_ref(v___y_3950_);
    return v_res_3955_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(
    mut v_msgData_3956_: *mut leanh::LeanObject,
    mut v___y_3957_: *mut leanh::LeanObject,
    mut v___y_3958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3960_: u8 = 0;
    let mut v___x_3961_: u8 = 0;
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = 0;
    v___x_3961_ = 0;
    v___x_3962_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(v_msgData_3956_, v___x_3960_, v___x_3961_, v___y_3957_, v___y_3958_);
    return v___x_3962_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3___boxed(
    mut v_msgData_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3967_ = l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(
        v_msgData_3963_,
        v___y_3964_,
        v___y_3965_,
    );
    leanh::lean_dec(v___y_3965_);
    leanh::lean_dec_ref(v___y_3964_);
    return v_res_3967_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2(
    mut v_msgData_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3972_: u8 = 0;
    let mut v___x_3973_: u8 = 0;
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = 1;
    v___x_3973_ = 0;
    v___x_3974_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2_spec__3(v_msgData_3968_, v___x_3972_, v___x_3973_, v___y_3969_, v___y_3970_);
    return v___x_3974_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2___boxed(
    mut v_msgData_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2(
        v_msgData_3975_,
        v___y_3976_,
        v___y_3977_,
    );
    leanh::lean_dec(v___y_3977_);
    leanh::lean_dec_ref(v___y_3976_);
    return v_res_3979_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0(
    mut v_a_3980_: *mut leanh::LeanObject,
    mut v_as_3981_: *mut leanh::LeanObject,
    mut v_i_3982_: usize,
    mut v_stop_3983_: usize,
) -> u8 {
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: usize = 0;
    let mut v___x_3988_: usize = 0;
    let mut v___x_3990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3984_ = lean_usize_dec_eq(v_i_3982_, v_stop_3983_);
                if v___x_3984_ == 0 {
                    v___x_3985_ = lean_array_uget_borrowed(v_as_3981_, v_i_3982_);
                    v___x_3986_ = lean_name_eq(v_a_3980_, v___x_3985_);
                    if v___x_3986_ == 0 {
                        v___x_3987_ = 1usize;
                        v___x_3988_ = lean_usize_add(v_i_3982_, v___x_3987_);
                        v_i_3982_ = v___x_3988_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3986_;
                    }
                } else {
                    v___x_3990_ = 0;
                    return v___x_3990_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0___boxed(
    mut v_a_3991_: *mut leanh::LeanObject,
    mut v_as_3992_: *mut leanh::LeanObject,
    mut v_i_3993_: *mut leanh::LeanObject,
    mut v_stop_3994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3995_: usize = 0;
    let mut v_stop_boxed_3996_: usize = 0;
    let mut v_res_3997_: u8 = 0;
    let mut v_r_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3995_ = leanh::lean_unbox_usize(v_i_3993_);
    leanh::lean_dec(v_i_3993_);
    v_stop_boxed_3996_ = leanh::lean_unbox_usize(v_stop_3994_);
    leanh::lean_dec(v_stop_3994_);
    v_res_3997_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0(v_a_3991_, v_as_3992_, v_i_boxed_3995_, v_stop_boxed_3996_);
    leanh::lean_dec_ref(v_as_3992_);
    leanh::lean_dec(v_a_3991_);
    v_r_3998_ = leanh::lean_box((v_res_3997_) as usize);
    return v_r_3998_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0(
    mut v_as_3999_: *mut leanh::LeanObject,
    mut v_a_4000_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: u8 = 0;
    v___x_4001_ = leanh::lean_unsigned_to_nat(0);
    v___x_4002_ = lean_array_get_size(v_as_3999_);
    v___x_4003_ = lean_nat_dec_lt(v___x_4001_, v___x_4002_);
    if v___x_4003_ == 0 {
        return v___x_4003_;
    } else {
        if v___x_4003_ == 0 {
            return v___x_4003_;
        } else {
            let mut v___x_4004_: usize = 0;
            let mut v___x_4005_: usize = 0;
            let mut v___x_4006_: u8 = 0;
            v___x_4004_ = 0usize;
            v___x_4005_ = lean_usize_of_nat(v___x_4002_);
            v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0_spec__0(v_a_4000_, v_as_3999_, v___x_4004_, v___x_4005_);
            return v___x_4006_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0___boxed(
    mut v_as_4007_: *mut leanh::LeanObject,
    mut v_a_4008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4009_: u8 = 0;
    let mut v_r_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4009_ = l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0(
        v_as_4007_, v_a_4008_,
    );
    leanh::lean_dec(v_a_4008_);
    leanh::lean_dec_ref(v_as_4007_);
    v_r_4010_ = leanh::lean_box((v_res_4009_) as usize);
    return v_r_4010_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__0;
    v___x_4013_ = l_Lean_stringToMessageData(v___x_4012_);
    return v___x_4013_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__2;
    v___x_4016_ = l_Lean_stringToMessageData(v___x_4015_);
    return v___x_4016_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__4;
    v___x_4019_ = l_Lean_stringToMessageData(v___x_4018_);
    return v___x_4019_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__6;
    v___x_4022_ = l_Lean_stringToMessageData(v___x_4021_);
    return v___x_4022_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4023_ = l_Lean_crossEmoji;
    v___x_4024_ = l_Lean_stringToMessageData(v___x_4023_);
    return v___x_4024_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4025_ = l_Lean_checkEmoji;
    v___x_4026_ = l_Lean_stringToMessageData(v___x_4025_);
    return v___x_4026_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(
    mut v_tk_4029_: *mut leanh::LeanObject,
    mut v___x_4030_: *mut leanh::LeanObject,
    mut v___x_4031_: *mut leanh::LeanObject,
    mut v_as_4032_: *mut leanh::LeanObject,
    mut v_sz_4033_: usize,
    mut v_i_4034_: usize,
    mut v_b_4035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: usize = 0;
    let mut v___x_4040_: usize = 0;
    let mut v___x_4042_: u8 = 0;
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v_snd_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v_a_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDecl_4054_: u8 = 0;
    let mut v_givenName_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modName_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: u8 = 0;
    let mut v___y_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4085_: u8 = 0;
    let mut v___y_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4087_: u8 = 0;
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4094_: u8 = 0;
    let mut v___y_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: u8 = 0;
    let mut v___y_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4100_: u8 = 0;
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4109_: u8 = 0;
    let mut v_unused_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4042_ = lean_usize_dec_lt(v_i_4034_, v_sz_4033_);
                if v___x_4042_ == 0 {
                    leanh::lean_dec_ref(v___x_4031_);
                    v___x_4043_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4043_, 0, v_b_4035_);
                    return v___x_4043_;
                } else {
                    v_snd_4044_ = leanh::lean_ctor_get(v_b_4035_, 1);
                    v_fst_4045_ = leanh::lean_ctor_get(v_b_4035_, 0);
                    v_isSharedCheck_4111_ = (!leanh::lean_is_exclusive(v_b_4035_)) as u8;
                    if v_isSharedCheck_4111_ == 0 {
                        v___x_4047_ = v_b_4035_;
                        v_isShared_4048_ = v_isSharedCheck_4111_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4044_);
                        leanh::lean_inc(v_fst_4045_);
                        leanh::lean_dec(v_b_4035_);
                        v___x_4047_ = leanh::lean_box(0);
                        v_isShared_4048_ = v_isSharedCheck_4111_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4039_ = 1usize;
                v___x_4040_ = lean_usize_add(v_i_4034_, v___x_4039_);
                v_i_4034_ = v___x_4040_;
                v_b_4035_ = v_a_4038_;
                state = 0;
                continue;
            }
            2 => {
                v_snd_4049_ = leanh::lean_ctor_get(v_snd_4044_, 1);
                v_isSharedCheck_4109_ = (!leanh::lean_is_exclusive(v_snd_4044_)) as u8;
                if v_isSharedCheck_4109_ == 0 {
                    v_unused_4110_ = leanh::lean_ctor_get(v_snd_4044_, 0);
                    leanh::lean_dec(v_unused_4110_);
                    v___x_4051_ = v_snd_4044_;
                    v_isShared_4052_ = v_isSharedCheck_4109_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4049_);
                    leanh::lean_dec(v_snd_4044_);
                    v___x_4051_ = leanh::lean_box(0);
                    v_isShared_4052_ = v_isSharedCheck_4109_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_4053_ = lean_array_uget_borrowed(v_as_4032_, v_i_4034_);
                v_isDecl_4054_ = leanh::lean_ctor_get_uint8(
                    v_a_4053_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_givenName_4055_ = leanh::lean_ctor_get(v_a_4053_, 0);
                v_modName_4056_ = leanh::lean_ctor_get(v_a_4053_, 1);
                if v_isDecl_4054_ == 0 {
                    v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__10;
                    v___y_4104_ = v___x_4107_;
                    state = 10;
                    continue;
                } else {
                    v___x_4108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__11;
                    v___y_4104_ = v___x_4108_;
                    state = 10;
                    continue;
                }
            }
            4 => {
                v___x_4061_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__1);
                leanh::lean_inc_ref_n(v___y_4060_, 2);
                v___x_4062_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4062_, 0, v___y_4060_);
                leanh::lean_ctor_set(v___x_4062_, 1, v___x_4061_);
                leanh::lean_inc(v_givenName_4055_);
                v___x_4063_ = l_Lean_MessageData_ofName(v_givenName_4055_);
                v___x_4064_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4064_, 0, v___x_4062_);
                leanh::lean_ctor_set(v___x_4064_, 1, v___x_4063_);
                v___x_4065_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__3);
                v___x_4066_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4066_, 0, v___x_4064_);
                leanh::lean_ctor_set(v___x_4066_, 1, v___x_4065_);
                leanh::lean_inc_ref(v___y_4058_);
                v___x_4067_ = l_Lean_stringToMessageData(v___y_4058_);
                v___x_4068_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4068_, 0, v___x_4066_);
                leanh::lean_ctor_set(v___x_4068_, 1, v___x_4067_);
                v___x_4069_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__5);
                v___x_4070_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4070_, 0, v___x_4068_);
                leanh::lean_ctor_set(v___x_4070_, 1, v___x_4069_);
                leanh::lean_inc(v_modName_4056_);
                v___x_4071_ = l_Lean_MessageData_ofName(v_modName_4056_);
                v___x_4072_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4072_, 0, v___x_4070_);
                leanh::lean_ctor_set(v___x_4072_, 1, v___x_4071_);
                v___x_4073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__7);
                v___x_4074_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4074_, 0, v___x_4072_);
                leanh::lean_ctor_set(v___x_4074_, 1, v___x_4073_);
                v___x_4075_ = lean_array_push(v_fst_4045_, v___x_4074_);
                v___x_4076_ = leanh::lean_box((v___y_4059_) as usize);
                if v_isShared_4052_ == 0 {
                    leanh::lean_ctor_set(v___x_4051_, 1, v___x_4076_);
                    leanh::lean_ctor_set(v___x_4051_, 0, v___y_4060_);
                    v___x_4078_ = v___x_4051_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 0, v___y_4060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 1, v___x_4076_);
                    v___x_4078_ = v_reuseFailAlloc_4082_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4048_ == 0 {
                    leanh::lean_ctor_set(v___x_4047_, 1, v___x_4078_);
                    leanh::lean_ctor_set(v___x_4047_, 0, v___x_4075_);
                    v___x_4080_ = v___x_4047_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4081_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 1, v___x_4078_);
                    v___x_4080_ = v_reuseFailAlloc_4081_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_4038_ = v___x_4080_;
                state = 1;
                continue;
            }
            7 => {
                v___x_4088_ = l_Lean_Syntax_isNone(v_tk_4029_);
                if v___x_4088_ == 0 {
                    if v___y_4085_ == 0 {
                        v___y_4058_ = v___y_4084_;
                        v___y_4059_ = v___y_4087_;
                        v___y_4060_ = v___y_4086_;
                        state = 4;
                        continue;
                    } else {
                        if v___x_4088_ == 0 {
                            leanh::lean_del_object(v___x_4051_);
                            leanh::lean_del_object(v___x_4047_);
                            v___x_4089_ = leanh::lean_box((v___y_4087_) as usize);
                            leanh::lean_inc_ref(v___y_4086_);
                            v___x_4090_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4090_, 0, v___y_4086_);
                            leanh::lean_ctor_set(v___x_4090_, 1, v___x_4089_);
                            v___x_4091_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4091_, 0, v_fst_4045_);
                            leanh::lean_ctor_set(v___x_4091_, 1, v___x_4090_);
                            v_a_4038_ = v___x_4091_;
                            state = 1;
                            continue;
                        } else {
                            v___y_4058_ = v___y_4084_;
                            v___y_4059_ = v___y_4087_;
                            v___y_4060_ = v___y_4086_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___y_4058_ = v___y_4084_;
                    v___y_4059_ = v___y_4087_;
                    v___y_4060_ = v___y_4086_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_4096_ = (leanh::lean_unbox(v_snd_4049_) as u8);
                if v___x_4096_ == 0 {
                    v___x_4097_ = (leanh::lean_unbox(v_snd_4049_) as u8);
                    leanh::lean_dec(v_snd_4049_);
                    v___y_4084_ = v___y_4093_;
                    v___y_4085_ = v___y_4094_;
                    v___y_4086_ = v___y_4095_;
                    v___y_4087_ = v___x_4097_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_4049_);
                    v___y_4084_ = v___y_4093_;
                    v___y_4085_ = v___y_4094_;
                    v___y_4086_ = v___y_4095_;
                    v___y_4087_ = v___y_4094_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4100_ == 0 {
                    v___x_4101_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8);
                    v___y_4093_ = v___y_4099_;
                    v___y_4094_ = v___y_4100_;
                    v___y_4095_ = v___x_4101_;
                    state = 8;
                    continue;
                } else {
                    v___x_4102_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9);
                    v___y_4093_ = v___y_4099_;
                    v___y_4094_ = v___y_4100_;
                    v___y_4095_ = v___x_4102_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v_isDecl_4054_ == 0 {
                    v___x_4105_ =
                        l_Array_contains___at___00Lean_Elab_Command_elabCheckAssertions_spec__0(
                            v___x_4030_,
                            v_givenName_4055_,
                        );
                    v___y_4099_ = v___y_4104_;
                    v___y_4100_ = v___x_4105_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_givenName_4055_);
                    leanh::lean_inc_ref(v___x_4031_);
                    v___x_4106_ =
                        l_Lean_Environment_contains(v___x_4031_, v_givenName_4055_, v___x_4042_);
                    v___y_4099_ = v___y_4104_;
                    v___y_4100_ = v___x_4106_;
                    state = 9;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___boxed(
    mut v_tk_4112_: *mut leanh::LeanObject,
    mut v___x_4113_: *mut leanh::LeanObject,
    mut v___x_4114_: *mut leanh::LeanObject,
    mut v_as_4115_: *mut leanh::LeanObject,
    mut v_sz_4116_: *mut leanh::LeanObject,
    mut v_i_4117_: *mut leanh::LeanObject,
    mut v_b_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4120_: usize = 0;
    let mut v_i_boxed_4121_: usize = 0;
    let mut v_res_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4120_ = leanh::lean_unbox_usize(v_sz_4116_);
    leanh::lean_dec(v_sz_4116_);
    v_i_boxed_4121_ = leanh::lean_unbox_usize(v_i_4117_);
    leanh::lean_dec(v_i_4117_);
    v_res_4122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(v_tk_4112_, v___x_4113_, v___x_4114_, v_as_4115_, v_sz_boxed_4120_, v_i_boxed_4121_, v_b_4118_);
    leanh::lean_dec_ref(v_as_4115_);
    leanh::lean_dec_ref(v___x_4113_);
    leanh::lean_dec(v_tk_4112_);
    return v_res_4122_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4123_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Command_elabImportPath_spec__1_spec__3___closed__0;
    v___x_4124_ = l_Lean_stringToMessageData(v___x_4123_);
    return v___x_4124_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4125_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__0_once),
        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__0,
    );
    v___x_4126_ = leanh::lean_unsigned_to_nat(1);
    v___x_4127_ = lean_mk_empty_array_with_capacity(v___x_4126_);
    v___x_4128_ = lean_array_push(v___x_4127_, v___x_4125_);
    return v___x_4128_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4129_: u8 = 0;
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4129_ = 1;
    v___x_4130_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__0_once),
        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__0,
    );
    v___x_4131_ = leanh::lean_box((v___x_4129_) as usize);
    v___x_4132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4132_, 0, v___x_4130_);
    leanh::lean_ctor_set(v___x_4132_, 1, v___x_4131_);
    return v___x_4132_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__2_once),
        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__2,
    );
    v___x_4134_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__1_once),
        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__1,
    );
    v___x_4135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4135_, 0, v___x_4134_);
    leanh::lean_ctor_set(v___x_4135_, 1, v___x_4133_);
    return v___x_4135_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_Elab_Command_elabCheckAssertions___closed__4;
    v___x_4138_ = l_Lean_stringToMessageData(v___x_4137_);
    return v___x_4138_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l_Lean_Elab_Command_elabCheckAssertions___closed__6;
    v___x_4141_ = l_Lean_stringToMessageData(v___x_4140_);
    return v___x_4141_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__7_once),
        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__7,
    );
    v___x_4143_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__9);
    v___x_4144_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4144_, 0, v___x_4143_);
    leanh::lean_ctor_set(v___x_4144_, 1, v___x_4142_);
    return v___x_4144_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Lean_Elab_Command_elabCheckAssertions___closed__9;
    v___x_4147_ = l_Lean_stringToMessageData(v___x_4146_);
    return v___x_4147_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4148_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCheckAssertions___closed__10_once),
        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__10,
    );
    v___x_4149_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg___closed__8);
    v___x_4150_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4150_, 0, v___x_4149_);
    leanh::lean_ctor_set(v___x_4150_, 1, v___x_4148_);
    return v___x_4150_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = l_Lean_Elab_Command_elabCheckAssertions___closed__13;
    v___x_4155_ = l_Lean_MessageData_ofFormat(v___x_4154_);
    return v___x_4155_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCheckAssertions___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4159_ = l_Lean_Elab_Command_elabCheckAssertions___closed__16;
    v___x_4160_ = l_Lean_MessageData_ofFormat(v___x_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Lean_Elab_Command_elabCheckAssertions(
    mut v_stx_4161_: *mut leanh::LeanObject,
    mut v_a_4162_: *mut leanh::LeanObject,
    mut v_a_4163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4174_: u8 = 0;
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4177_: usize = 0;
    let mut v___x_4178_: usize = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: u8 = 0;
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: u8 = 0;
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: u8 = 0;
    let mut v___x_4210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4168_ = lean_st_ref_get(v_a_4163_);
                v_env_4169_ = leanh::lean_ctor_get(v___x_4168_, 0);
                leanh::lean_inc_ref_n(v_env_4169_, 2);
                leanh::lean_dec(v___x_4168_);
                v___x_4170_ = leanh::lean_unsigned_to_nat(1);
                v_tk_4171_ = l_Lean_Syntax_getArg(v_stx_4161_, v___x_4170_);
                v___x_4172_ = l_Lean_Elab_Command_getSortedAssertExists(v_env_4169_);
                v___x_4207_ = lean_array_get_size(v___x_4172_);
                v___x_4208_ = leanh::lean_unsigned_to_nat(0);
                v___x_4209_ = lean_nat_dec_eq(v___x_4207_, v___x_4208_);
                if v___x_4209_ == 0 {
                    v___y_4174_ = v___x_4209_;
                    state = 2;
                    continue;
                } else {
                    v___x_4210_ = l_Lean_Syntax_isNone(v_tk_4171_);
                    v___y_4174_ = v___x_4210_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_4166_ = leanh::lean_box(0);
                v___x_4167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4167_, 0, v___x_4166_);
                return v___x_4167_;
            }
            2 => {
                if v___y_4174_ == 0 {
                    v___x_4175_ = l_Lean_Environment_allImportedModuleNames(v_env_4169_);
                    v___x_4176_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabCheckAssertions___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabCheckAssertions___closed__3_once
                        ),
                        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__3,
                    );
                    v_sz_4177_ = lean_array_size(v___x_4172_);
                    v___x_4178_ = 0usize;
                    v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(v_tk_4171_, v___x_4175_, v_env_4169_, v___x_4172_, v_sz_4177_, v___x_4178_, v___x_4176_);
                    leanh::lean_dec_ref(v___x_4172_);
                    leanh::lean_dec_ref(v___x_4175_);
                    if leanh::lean_obj_tag(v___x_4179_) == 0 {
                        v_a_4180_ = leanh::lean_ctor_get(v___x_4179_, 0);
                        leanh::lean_inc(v_a_4180_);
                        leanh::lean_dec_ref_known(v___x_4179_, 1);
                        v_snd_4181_ = leanh::lean_ctor_get(v_a_4180_, 1);
                        leanh::lean_inc(v_snd_4181_);
                        v_fst_4182_ = leanh::lean_ctor_get(v_a_4180_, 0);
                        leanh::lean_inc(v_fst_4182_);
                        leanh::lean_dec(v_a_4180_);
                        v_snd_4183_ = leanh::lean_ctor_get(v_snd_4181_, 1);
                        leanh::lean_inc(v_snd_4183_);
                        leanh::lean_dec(v_snd_4181_);
                        v___x_4184_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__5_once
                            ),
                            _init_l_Lean_Elab_Command_elabCheckAssertions___closed__5,
                        );
                        v___x_4185_ = lean_array_push(v_fst_4182_, v___x_4184_);
                        v___x_4186_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__8_once
                            ),
                            _init_l_Lean_Elab_Command_elabCheckAssertions___closed__8,
                        );
                        v___x_4187_ = lean_array_push(v___x_4185_, v___x_4186_);
                        v___x_4188_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__11_once
                            ),
                            _init_l_Lean_Elab_Command_elabCheckAssertions___closed__11,
                        );
                        v___x_4189_ = lean_array_push(v___x_4187_, v___x_4188_);
                        v___x_4190_ = lean_array_to_list(v___x_4189_);
                        v___x_4191_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabCheckAssertions___closed__14_once
                            ),
                            _init_l_Lean_Elab_Command_elabCheckAssertions___closed__14,
                        );
                        v___x_4192_ = l_Lean_MessageData_joinSep(v___x_4190_, v___x_4191_);
                        v___x_4193_ = (leanh::lean_unbox(v_snd_4183_) as u8);
                        leanh::lean_dec(v_snd_4183_);
                        if v___x_4193_ == 0 {
                            leanh::lean_dec(v_tk_4171_);
                            v___x_4194_ = l_Lean_logWarning___at___00Lean_Elab_Command_elabCheckAssertions_spec__2(v___x_4192_, v_a_4162_, v_a_4163_);
                            return v___x_4194_;
                        } else {
                            v___x_4195_ = l_Lean_Syntax_isNone(v_tk_4171_);
                            leanh::lean_dec(v_tk_4171_);
                            if v___x_4195_ == 0 {
                                leanh::lean_dec_ref(v___x_4192_);
                                state = 1;
                                continue;
                            } else {
                                v___x_4196_ = l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(v___x_4192_, v_a_4162_, v_a_4163_);
                                if leanh::lean_obj_tag(v___x_4196_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4196_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_4196_;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_tk_4171_);
                        v_a_4197_ = leanh::lean_ctor_get(v___x_4179_, 0);
                        v_isSharedCheck_4204_ =
                            (!leanh::lean_is_exclusive(v___x_4179_)) as u8;
                        if v_isSharedCheck_4204_ == 0 {
                            v___x_4199_ = v___x_4179_;
                            v_isShared_4200_ = v_isSharedCheck_4204_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4197_);
                            leanh::lean_dec(v___x_4179_);
                            v___x_4199_ = leanh::lean_box(0);
                            v_isShared_4200_ = v_isSharedCheck_4204_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4172_);
                    leanh::lean_dec(v_tk_4171_);
                    leanh::lean_dec_ref(v_env_4169_);
                    v___x_4205_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabCheckAssertions___closed__17
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabCheckAssertions___closed__17_once
                        ),
                        _init_l_Lean_Elab_Command_elabCheckAssertions___closed__17,
                    );
                    v___x_4206_ =
                        l_Lean_logInfo___at___00Lean_Elab_Command_elabCheckAssertions_spec__3(
                            v___x_4205_,
                            v_a_4162_,
                            v_a_4163_,
                        );
                    return v___x_4206_;
                }
            }
            3 => {
                if v_isShared_4200_ == 0 {
                    v___x_4202_ = v___x_4199_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
                    v___x_4202_ = v_reuseFailAlloc_4203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCheckAssertions___boxed(
    mut v_stx_4211_: *mut leanh::LeanObject,
    mut v_a_4212_: *mut leanh::LeanObject,
    mut v_a_4213_: *mut leanh::LeanObject,
    mut v_a_4214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4215_ = l_Lean_Elab_Command_elabCheckAssertions(v_stx_4211_, v_a_4212_, v_a_4213_);
    leanh::lean_dec(v_a_4213_);
    leanh::lean_dec_ref(v_a_4212_);
    leanh::lean_dec(v_stx_4211_);
    return v_res_4215_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1(
    mut v_tk_4216_: *mut leanh::LeanObject,
    mut v___x_4217_: *mut leanh::LeanObject,
    mut v___x_4218_: *mut leanh::LeanObject,
    mut v_as_4219_: *mut leanh::LeanObject,
    mut v_sz_4220_: usize,
    mut v_i_4221_: usize,
    mut v_b_4222_: *mut leanh::LeanObject,
    mut v___y_4223_: *mut leanh::LeanObject,
    mut v___y_4224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___redArg(v_tk_4216_, v___x_4217_, v___x_4218_, v_as_4219_, v_sz_4220_, v_i_4221_, v_b_4222_);
    return v___x_4226_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1___boxed(
    mut v_tk_4227_: *mut leanh::LeanObject,
    mut v___x_4228_: *mut leanh::LeanObject,
    mut v___x_4229_: *mut leanh::LeanObject,
    mut v_as_4230_: *mut leanh::LeanObject,
    mut v_sz_4231_: *mut leanh::LeanObject,
    mut v_i_4232_: *mut leanh::LeanObject,
    mut v_b_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4237_: usize = 0;
    let mut v_i_boxed_4238_: usize = 0;
    let mut v_res_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4237_ = leanh::lean_unbox_usize(v_sz_4231_);
    leanh::lean_dec(v_sz_4231_);
    v_i_boxed_4238_ = leanh::lean_unbox_usize(v_i_4232_);
    leanh::lean_dec(v_i_4232_);
    v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabCheckAssertions_spec__1(v_tk_4227_, v___x_4228_, v___x_4229_, v_as_4230_, v_sz_boxed_4237_, v_i_boxed_4238_, v_b_4233_, v___y_4234_, v___y_4235_);
    leanh::lean_dec(v___y_4235_);
    leanh::lean_dec_ref(v___y_4234_);
    leanh::lean_dec_ref(v_as_4230_);
    leanh::lean_dec_ref(v___x_4228_);
    leanh::lean_dec(v_tk_4227_);
    return v_res_4239_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1()
-> *mut leanh::LeanObject {
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4253_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4254_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__1;
    v___x_4255_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3;
    v___x_4256_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabCheckAssertions___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_4257_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4253_,
        v___x_4254_,
        v___x_4255_,
        v___x_4256_,
    );
    return v___x_4257_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___boxed(
    mut v_a_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1();
    return v_res_4259_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3()
-> *mut leanh::LeanObject {
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1___closed__3;
    v___x_4263_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___closed__0;
    v___x_4264_ = l_Lean_addBuiltinDocString(v___x_4262_, v___x_4263_);
    return v___x_4264_;
}
pub unsafe fn l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3___boxed(
    mut v_a_4265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4266_ = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3();
    return v_res_4266_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_AssertExists(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_AssertExists_2003177635____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Command_assertExistsExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Elab_Command_assertExistsExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabImportPath___regBuiltin_Lean_Elab_Command_elabImportPath_docString__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotExists___regBuiltin_Lean_Elab_Command_elabAssertNotExists_docString__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabAssertNotImported___regBuiltin_Lean_Elab_Command_elabAssertNotImported_docString__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_AssertExists_0__Lean_Elab_Command_elabCheckAssertions___regBuiltin_Lean_Elab_Command_elabCheckAssertions_docString__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_AssertExists(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_AssertExists(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AssertExists(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_AssertExists(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_AssertExists(builtin);
}