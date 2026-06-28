// Lean compiler output
// Module: Lean.Compiler.CSimpAttr
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.ExtraModUses
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_replaceRef, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_ensureAttrDeclIsPublic,
    l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg, l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_isAppOfArity, l_Lean_mkConst,
};
use crate::r#gen::Lean::ExtraModUses::{
    initialize_Lean_ExtraModUses, l___private_Lean_ExtraModUses_0__Lean_extraModUses,
    l_Lean_indirectModUseExt, l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
    runtime_initialize_Lean_ExtraModUses,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_hash, l_Lean_Level_isParam};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_addCore___redArg,
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_registerSimpleScopedEnvExtension___redArg,
    runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Lean::Util::Recognizers::{
    initialize_Lean_Util_Recognizers, runtime_initialize_Lean_Util_Recognizers,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_CSimp_instInhabitedEntry_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_CSimp_instInhabitedEntry: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_instInhabitedEntry_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_CSimp_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_CSimp_instInhabitedState: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_CSimp_State_switch as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [67, 83, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 120, 116, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,8543197020067251012 as *mut LeanObject] };
static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,2506120210329473605 as *mut LeanObject] };
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,16700278000057647119 as *mut LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_CSimp_add___closed__0_value: LeanStringObject<103> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 103,
    m_capacity: 103,
    m_length: 102,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 115, 105, 109, 112, 39, 32, 116, 104, 101,
        111, 114, 101, 109, 44, 32, 111, 110, 108, 121, 32, 99, 111, 110, 115, 116, 97, 110, 116,
        32, 114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116, 32, 116, 104, 101, 111, 114, 101,
        109, 115, 32, 40, 101, 46, 103, 46, 44, 32, 96, 64, 102, 32, 61, 32, 64, 103, 96, 41, 32,
        97, 114, 101, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 115, 117, 112, 112, 111,
        114, 116, 101, 100, 46, 0,
    ],
};
static mut l_Lean_Compiler_CSimp_add___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_CSimp_add___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_CSimp_add___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_CSimp_add___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_value:
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
    m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_value
        ) as *mut LeanObject,
        11079354408986465895 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_value:
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
    m_data: [67, 83, 105, 109, 112, 65, 116, 116, 114, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_value
        ) as *mut LeanObject,
        2541629466078937915 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        11902246563960517958 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__3_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,12348749176669000783 as *mut LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__4_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,8798584843508670593 as *mut LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__5_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__value) as *mut LeanObject,6759957689071080516 as *mut LeanObject] };
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10_value:
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
    m_data: [105, 110, 105, 116, 70, 110, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__9_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__10_value
        ) as *mut LeanObject,
        14890345188404749281 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12_value:
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
    m_data: [99, 115, 105, 109, 112, 0],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value:
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
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__12_value
        ) as *mut LeanObject,
        6868535136644065322 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16_value:
    LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111,
        114, 101, 109, 32, 102, 111, 114, 32, 116, 104, 101, 32, 99, 111, 109, 112, 105, 108, 101,
        114, 0,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17_value:
    LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__13_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__16_value
        ) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__17_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__14_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__15_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0_value: LeanStringObject<863> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 863, m_capacity: 863, m_length: 862, m_data: [84, 97, 103, 115, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 44, 32, 119, 104, 105, 99, 104, 32, 97, 108, 108, 111, 119, 32, 111, 110, 101, 32, 118, 97, 108, 117, 101, 32, 116, 111, 32, 98, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 97, 110, 111, 116, 104, 101, 114, 32, 101, 113, 117, 97, 108, 32, 118, 97, 108, 117, 101, 10, 105, 110, 32, 99, 111, 109, 112, 105, 108, 101, 100, 32, 99, 111, 100, 101, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 116, 121, 112, 105, 99, 97, 108, 108, 121, 32, 117, 115, 101, 100, 32, 116, 111, 32, 114, 101, 112, 108, 97, 99, 101, 32, 97, 32, 115, 108, 111, 119, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 119, 104, 111, 115, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 105, 115, 32, 99, 111, 110, 118, 101, 110, 105, 101, 110, 116, 10, 105, 110, 32, 112, 114, 111, 111, 102, 115, 32, 119, 105, 116, 104, 32, 97, 32, 102, 97, 115, 116, 101, 114, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 111, 114, 32, 116, 111, 32, 109, 97, 107, 101, 32, 110, 111, 110, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 99, 111, 109, 112, 117, 116, 97, 98, 108, 101, 46, 32, 73, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 44, 10, 109, 97, 110, 121, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 115, 32, 111, 110, 32, 108, 105, 115, 116, 115, 32, 97, 110, 100, 32, 97, 114, 114, 97, 121, 115, 32, 97, 114, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 116, 97, 105, 108, 45, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 115, 46, 10, 10, 65, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 32, 99, 97, 110, 110, 111, 116, 32, 116, 97, 107, 101, 32, 97, 110, 121, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 110, 100, 32, 109, 117, 115, 116, 32, 112, 114, 111, 118, 101, 32, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 96, 64, 102, 32, 61, 32, 64, 103, 96, 10, 119, 104, 101, 114, 101, 32, 96, 102, 96, 32, 97, 110, 100, 32, 96, 103, 96, 32, 109, 97, 121, 32, 98, 101, 32, 97, 114, 98, 105, 116, 114, 97, 114, 121, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 46, 32, 73, 110, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 116, 104, 101, 111, 114, 101, 109, 32, 116, 97, 103, 103, 101, 100, 10, 96, 64, 91, 99, 115, 105, 109, 112, 93, 96, 44, 32, 97, 110, 121, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 96, 102, 96, 32, 105, 115, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 96, 103, 96, 32, 105, 110, 32, 99, 111, 109, 112, 105, 108, 101, 100, 32, 99, 111, 100, 101, 44, 32, 98, 117, 116, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 10, 116, 104, 101, 111, 114, 121, 46, 32, 73, 110, 32, 116, 104, 105, 115, 32, 115, 101, 110, 115, 101, 44, 32, 96, 64, 91, 99, 115, 105, 109, 112, 93, 96, 32, 105, 115, 32, 97, 32, 115, 97, 102, 101, 114, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 116, 111, 32, 96, 64, 91, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 95, 98, 121, 93, 96, 46, 10, 10, 72, 111, 119, 101, 118, 101, 114, 32, 105, 116, 32, 105, 115, 32, 115, 116, 105, 108, 108, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 116, 111, 32, 114, 101, 103, 105, 115, 116, 101, 114, 32, 117, 110, 115, 111, 117, 110, 100, 32, 96, 64, 91, 99, 115, 105, 109, 112, 93, 96, 32, 108, 101, 109, 109, 97, 115, 32, 98, 121, 32, 117, 115, 105, 110, 103, 32, 96, 117, 110, 115, 97, 102, 101, 96, 32, 111, 114, 32, 117, 110, 115, 111, 117, 110, 100, 10, 97, 120, 105, 111, 109, 115, 32, 40, 108, 105, 107, 101, 32, 96, 115, 111, 114, 114, 121, 65, 120, 96, 41, 46, 10, 0]};
static mut l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__3_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__10_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0() -> *mut LeanObject
{
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    v___x_2264_ = lean_box(0);
    v___x_2265_ = lean_unsigned_to_nat(16);
    v___x_2266_ = lean_mk_array(v___x_2265_, v___x_2264_);
    return v___x_2266_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1() -> *mut LeanObject
{
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    v___x_2267_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__0,
    );
    v___x_2268_ = lean_unsigned_to_nat(0);
    v___x_2269_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2269_, 0, v___x_2268_);
    lean_ctor_set(v___x_2269_, 1, v___x_2267_);
    return v___x_2269_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2() -> *mut LeanObject
{
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    v___x_2270_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2270_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3() -> *mut LeanObject
{
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    v___x_2271_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__2,
    );
    v___x_2272_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2272_, 0, v___x_2271_);
    return v___x_2272_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4() -> *mut LeanObject
{
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    v___x_2273_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__3,
    );
    v___x_2274_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__1,
    );
    v___x_2275_ = 1;
    v___x_2276_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_2276_, 0, v___x_2274_);
    lean_ctor_set(v___x_2276_, 1, v___x_2273_);
    lean_ctor_set_uint8(
        v___x_2276_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_2275_,
    );
    return v___x_2276_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5() -> *mut LeanObject
{
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    v___x_2277_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__4,
    );
    v___x_2278_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2278_, 0, v___x_2277_);
    lean_ctor_set(v___x_2278_, 1, v___x_2277_);
    return v___x_2278_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    v___x_2279_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5,
    );
    return v___x_2279_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_instInhabitedState() -> *mut LeanObject {
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    v___x_2280_ = l_Lean_Compiler_CSimp_instInhabitedState_default;
    return v___x_2280_;
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(
    mut v_m_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_2282_: u8 = 0;
    let mut v_map_u2081_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2287_: u8 = 0;
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2282_ = lean_ctor_get_uint8(
                    v_m_2281_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2282_ == 0 {
                    return v_m_2281_;
                } else {
                    v_map_u2081_2283_ = lean_ctor_get(v_m_2281_, 0);
                    v_map_u2082_2284_ = lean_ctor_get(v_m_2281_, 1);
                    v_isSharedCheck_2292_ = (!lean_is_exclusive(v_m_2281_)) as u8;
                    if v_isSharedCheck_2292_ == 0 {
                        v___x_2286_ = v_m_2281_;
                        v_isShared_2287_ = v_isSharedCheck_2292_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_2284_);
                        lean_inc(v_map_u2081_2283_);
                        lean_dec(v_m_2281_);
                        v___x_2286_ = lean_box(0);
                        v_isShared_2287_ = v_isSharedCheck_2292_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2288_ = 0;
                if v_isShared_2287_ == 0 {
                    v___x_2290_ = v___x_2286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_map_u2081_2283_);
                    lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_map_u2082_2284_);
                    v___x_2290_ = v_reuseFailAlloc_2291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2290_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2288_,
                );
                return v___x_2290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0(
    mut v_00_u03b2_2293_: *mut LeanObject,
    mut v_m_2294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    v___x_2295_ =
        l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(v_m_2294_);
    return v___x_2295_;
}
pub unsafe fn l_Lean_Compiler_CSimp_State_switch(
    mut v_x_2296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmNames_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2297_ = lean_ctor_get(v_x_2296_, 0);
                v_thmNames_2298_ = lean_ctor_get(v_x_2296_, 1);
                v_isSharedCheck_2307_ = (!lean_is_exclusive(v_x_2296_)) as u8;
                if v_isSharedCheck_2307_ == 0 {
                    v___x_2300_ = v_x_2296_;
                    v_isShared_2301_ = v_isSharedCheck_2307_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_thmNames_2298_);
                    lean_inc(v_map_2297_);
                    lean_dec(v_x_2296_);
                    v___x_2300_ = lean_box(0);
                    v_isShared_2301_ = v_isSharedCheck_2307_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2302_ =
                    l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(
                        v_map_2297_,
                    );
                v___x_2303_ =
                    l_Lean_SMap_switch___at___00Lean_Compiler_CSimp_State_switch_spec__0___redArg(
                        v_thmNames_2298_,
                    );
                if v_isShared_2301_ == 0 {
                    lean_ctor_set(v___x_2300_, 1, v___x_2303_);
                    lean_ctor_set(v___x_2300_, 0, v___x_2302_);
                    v___x_2305_ = v___x_2300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2302_);
                    lean_ctor_set(v_reuseFailAlloc_2306_, 1, v___x_2303_);
                    v___x_2305_ = v_reuseFailAlloc_2306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_(
    mut v_x_2308_: *mut LeanObject,
    mut v_a_2309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2310_, 0, v_a_2309_);
    lean_inc_ref_n(v___x_2310_, 2);
    v___x_2311_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2311_, 0, v___x_2310_);
    lean_ctor_set(v___x_2311_, 1, v___x_2310_);
    lean_ctor_set(v___x_2311_, 2, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2____boxed(
    mut v_x_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2314_: *mut LeanObject = core::ptr::null_mut();
    v_res_2314_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_(v_x_2312_, v_a_2313_);
    lean_dec_ref(v_x_2312_);
    return v_res_2314_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_2315_: *mut LeanObject,
    mut v_x_2316_: *mut LeanObject,
    mut v_x_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2319_ = lean_ctor_get(v_x_2315_, 0);
                v_vs_2320_ = lean_ctor_get(v_x_2315_, 1);
                v_isSharedCheck_2344_ = (!lean_is_exclusive(v_x_2315_)) as u8;
                if v_isSharedCheck_2344_ == 0 {
                    v___x_2322_ = v_x_2315_;
                    v_isShared_2323_ = v_isSharedCheck_2344_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2320_);
                    lean_inc(v_ks_2319_);
                    lean_dec(v_x_2315_);
                    v___x_2322_ = lean_box(0);
                    v_isShared_2323_ = v_isSharedCheck_2344_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2324_ = lean_array_get_size(v_ks_2319_);
                v___x_2325_ = lean_nat_dec_lt(v_x_2316_, v___x_2324_);
                if v___x_2325_ == 0 {
                    lean_dec(v_x_2316_);
                    v___x_2326_ = lean_array_push(v_ks_2319_, v_x_2317_);
                    v___x_2327_ = lean_array_push(v_vs_2320_, v_x_2318_);
                    if v_isShared_2323_ == 0 {
                        lean_ctor_set(v___x_2322_, 1, v___x_2327_);
                        lean_ctor_set(v___x_2322_, 0, v___x_2326_);
                        v___x_2329_ = v___x_2322_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2326_);
                        lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2327_);
                        v___x_2329_ = v_reuseFailAlloc_2330_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2331_ = lean_array_fget_borrowed(v_ks_2319_, v_x_2316_);
                    v___x_2332_ = lean_name_eq(v_x_2317_, v_k_x27_2331_);
                    if v___x_2332_ == 0 {
                        if v_isShared_2323_ == 0 {
                            v___x_2334_ = v___x_2322_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_ks_2319_);
                            lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_vs_2320_);
                            v___x_2334_ = v_reuseFailAlloc_2338_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2339_ = lean_array_fset(v_ks_2319_, v_x_2316_, v_x_2317_);
                        v___x_2340_ = lean_array_fset(v_vs_2320_, v_x_2316_, v_x_2318_);
                        lean_dec(v_x_2316_);
                        if v_isShared_2323_ == 0 {
                            lean_ctor_set(v___x_2322_, 1, v___x_2340_);
                            lean_ctor_set(v___x_2322_, 0, v___x_2339_);
                            v___x_2342_ = v___x_2322_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2339_);
                            lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2340_);
                            v___x_2342_ = v_reuseFailAlloc_2343_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2329_;
            }
            3 => {
                v___x_2335_ = lean_unsigned_to_nat(1);
                v___x_2336_ = lean_nat_add(v_x_2316_, v___x_2335_);
                lean_dec(v_x_2316_);
                v_x_2315_ = v___x_2334_;
                v_x_2316_ = v___x_2336_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_2345_: *mut LeanObject,
    mut v_k_2346_: *mut LeanObject,
    mut v_v_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    v___x_2348_ = lean_unsigned_to_nat(0);
    v___x_2349_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_2345_, v___x_2348_, v_k_2346_, v_v_2347_);
    return v___x_2349_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u64 = 0;
    v___x_2350_ = lean_unsigned_to_nat(1723);
    v___x_2351_ = lean_uint64_of_nat(v___x_2350_);
    return v___x_2351_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2352_: usize = 0;
    let mut v___x_2353_: usize = 0;
    let mut v___x_2354_: usize = 0;
    v___x_2352_ = 5usize;
    v___x_2353_ = 1usize;
    v___x_2354_ = lean_usize_shift_left(v___x_2353_, v___x_2352_);
    return v___x_2354_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2355_: usize = 0;
    let mut v___x_2356_: usize = 0;
    let mut v___x_2357_: usize = 0;
    v___x_2355_ = 1usize;
    v___x_2356_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2357_ = lean_usize_sub(v___x_2356_, v___x_2355_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    v___x_2358_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2358_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_2359_: *mut LeanObject,
    mut v_x_2360_: usize,
    mut v_x_2361_: usize,
    mut v_x_2362_: *mut LeanObject,
    mut v_x_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: usize = 0;
    let mut v___x_2366_: usize = 0;
    let mut v___x_2367_: usize = 0;
    let mut v___x_2368_: usize = 0;
    let mut v_j_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v_v_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2389_: u8 = 0;
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_node_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: usize = 0;
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut v_unused_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: u8 = 0;
    let mut v_ks_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: usize = 0;
    let mut v___x_2426_: u8 = 0;
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    let mut v_reuseFailAlloc_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2359_) == 0 {
                    v_es_2364_ = lean_ctor_get(v_x_2359_, 0);
                    v___x_2365_ = 5usize;
                    v___x_2366_ = 1usize;
                    v___x_2367_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2368_ = lean_usize_land(v_x_2360_, v___x_2367_);
                    v_j_2369_ = lean_usize_to_nat(v___x_2368_);
                    v___x_2370_ = lean_array_get_size(v_es_2364_);
                    v___x_2371_ = lean_nat_dec_lt(v_j_2369_, v___x_2370_);
                    if v___x_2371_ == 0 {
                        lean_dec(v_j_2369_);
                        lean_dec(v_x_2363_);
                        lean_dec(v_x_2362_);
                        return v_x_2359_;
                    } else {
                        lean_inc_ref(v_es_2364_);
                        v_isSharedCheck_2408_ = (!lean_is_exclusive(v_x_2359_)) as u8;
                        if v_isSharedCheck_2408_ == 0 {
                            v_unused_2409_ = lean_ctor_get(v_x_2359_, 0);
                            lean_dec(v_unused_2409_);
                            v___x_2373_ = v_x_2359_;
                            v_isShared_2374_ = v_isSharedCheck_2408_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2359_);
                            v___x_2373_ = lean_box(0);
                            v_isShared_2374_ = v_isSharedCheck_2408_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2410_ = lean_ctor_get(v_x_2359_, 0);
                    v_vs_2411_ = lean_ctor_get(v_x_2359_, 1);
                    v_isSharedCheck_2431_ = (!lean_is_exclusive(v_x_2359_)) as u8;
                    if v_isSharedCheck_2431_ == 0 {
                        v___x_2413_ = v_x_2359_;
                        v_isShared_2414_ = v_isSharedCheck_2431_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2411_);
                        lean_inc(v_ks_2410_);
                        lean_dec(v_x_2359_);
                        v___x_2413_ = lean_box(0);
                        v_isShared_2414_ = v_isSharedCheck_2431_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2375_ = lean_array_fget(v_es_2364_, v_j_2369_);
                v___x_2376_ = lean_box(0);
                v_xs_x27_2377_ = lean_array_fset(v_es_2364_, v_j_2369_, v___x_2376_);
                match lean_obj_tag(v_v_2375_) {
                    0 => {
                        v_key_2384_ = lean_ctor_get(v_v_2375_, 0);
                        v_val_2385_ = lean_ctor_get(v_v_2375_, 1);
                        v_isSharedCheck_2395_ = (!lean_is_exclusive(v_v_2375_)) as u8;
                        if v_isSharedCheck_2395_ == 0 {
                            v___x_2387_ = v_v_2375_;
                            v_isShared_2388_ = v_isSharedCheck_2395_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2385_);
                            lean_inc(v_key_2384_);
                            lean_dec(v_v_2375_);
                            v___x_2387_ = lean_box(0);
                            v_isShared_2388_ = v_isSharedCheck_2395_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2396_ = lean_ctor_get(v_v_2375_, 0);
                        v_isSharedCheck_2406_ = (!lean_is_exclusive(v_v_2375_)) as u8;
                        if v_isSharedCheck_2406_ == 0 {
                            v___x_2398_ = v_v_2375_;
                            v_isShared_2399_ = v_isSharedCheck_2406_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2396_);
                            lean_dec(v_v_2375_);
                            v___x_2398_ = lean_box(0);
                            v_isShared_2399_ = v_isSharedCheck_2406_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2407_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2407_, 0, v_x_2362_);
                        lean_ctor_set(v___x_2407_, 1, v_x_2363_);
                        v___y_2379_ = v___x_2407_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2380_ = lean_array_fset(v_xs_x27_2377_, v_j_2369_, v___y_2379_);
                lean_dec(v_j_2369_);
                if v_isShared_2374_ == 0 {
                    lean_ctor_set(v___x_2373_, 0, v___x_2380_);
                    v___x_2382_ = v___x_2373_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
                    v___x_2382_ = v_reuseFailAlloc_2383_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2382_;
            }
            4 => {
                v___x_2389_ = lean_name_eq(v_x_2362_, v_key_2384_);
                if v___x_2389_ == 0 {
                    lean_del_object(v___x_2387_);
                    v___x_2390_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2384_,
                        v_val_2385_,
                        v_x_2362_,
                        v_x_2363_,
                    );
                    v___x_2391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2391_, 0, v___x_2390_);
                    v___y_2379_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2385_);
                    lean_dec(v_key_2384_);
                    if v_isShared_2388_ == 0 {
                        lean_ctor_set(v___x_2387_, 1, v_x_2363_);
                        lean_ctor_set(v___x_2387_, 0, v_x_2362_);
                        v___x_2393_ = v___x_2387_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_x_2362_);
                        lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_x_2363_);
                        v___x_2393_ = v_reuseFailAlloc_2394_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2379_ = v___x_2393_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2400_ = lean_usize_shift_right(v_x_2360_, v___x_2365_);
                v___x_2401_ = lean_usize_add(v_x_2361_, v___x_2366_);
                v___x_2402_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_node_2396_, v___x_2400_, v___x_2401_, v_x_2362_, v_x_2363_);
                if v_isShared_2399_ == 0 {
                    lean_ctor_set(v___x_2398_, 0, v___x_2402_);
                    v___x_2404_ = v___x_2398_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
                    v___x_2404_ = v_reuseFailAlloc_2405_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2379_ = v___x_2404_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2414_ == 0 {
                    v___x_2416_ = v___x_2413_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_ks_2410_);
                    lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_vs_2411_);
                    v___x_2416_ = v_reuseFailAlloc_2430_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2417_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v___x_2416_, v_x_2362_, v_x_2363_);
                v___x_2425_ = 7usize;
                v___x_2426_ = lean_usize_dec_le(v___x_2425_, v_x_2361_);
                if v___x_2426_ == 0 {
                    v___x_2427_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2417_);
                    v___x_2428_ = lean_unsigned_to_nat(4);
                    v___x_2429_ = lean_nat_dec_lt(v___x_2427_, v___x_2428_);
                    lean_dec(v___x_2427_);
                    v___y_2419_ = v___x_2429_;
                    state = 10;
                    continue;
                } else {
                    v___y_2419_ = v___x_2426_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2419_ == 0 {
                    v_ks_2420_ = lean_ctor_get(v_newNode_2417_, 0);
                    lean_inc_ref(v_ks_2420_);
                    v_vs_2421_ = lean_ctor_get(v_newNode_2417_, 1);
                    lean_inc_ref(v_vs_2421_);
                    lean_dec_ref(v_newNode_2417_);
                    v___x_2422_ = lean_unsigned_to_nat(0);
                    v___x_2423_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_2424_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_x_2361_, v_ks_2420_, v_vs_2421_, v___x_2422_, v___x_2423_);
                    lean_dec_ref(v_vs_2421_);
                    lean_dec_ref(v_ks_2420_);
                    return v___x_2424_;
                } else {
                    return v_newNode_2417_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_2432_: usize,
    mut v_keys_2433_: *mut LeanObject,
    mut v_vals_2434_: *mut LeanObject,
    mut v_i_2435_: *mut LeanObject,
    mut v_entries_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: u8 = 0;
    let mut v_k_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: u64 = 0;
    let mut v_h_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: usize = 0;
    let mut v___x_2447_: usize = 0;
    let mut v___x_2448_: usize = 0;
    let mut v_h_2449_: usize = 0;
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: u64 = 0;
    let mut v_hash_2454_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2437_ = lean_array_get_size(v_keys_2433_);
                v___x_2438_ = lean_nat_dec_lt(v_i_2435_, v___x_2437_);
                if v___x_2438_ == 0 {
                    lean_dec(v_i_2435_);
                    return v_entries_2436_;
                } else {
                    v_k_2439_ = lean_array_fget_borrowed(v_keys_2433_, v_i_2435_);
                    v_v_2440_ = lean_array_fget_borrowed(v_vals_2434_, v_i_2435_);
                    if lean_obj_tag(v_k_2439_) == 0 {
                        v___x_2453_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                        v___y_2442_ = v___x_2453_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2454_ = lean_ctor_get_uint64(
                            v_k_2439_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_2442_ = v_hash_2454_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2443_ = lean_uint64_to_usize(v___y_2442_);
                v___x_2444_ = 5usize;
                v___x_2445_ = lean_unsigned_to_nat(1);
                v___x_2446_ = 1usize;
                v___x_2447_ = lean_usize_sub(v_depth_2432_, v___x_2446_);
                v___x_2448_ = lean_usize_mul(v___x_2444_, v___x_2447_);
                v_h_2449_ = lean_usize_shift_right(v_h_2443_, v___x_2448_);
                v___x_2450_ = lean_nat_add(v_i_2435_, v___x_2445_);
                lean_dec(v_i_2435_);
                lean_inc(v_v_2440_);
                lean_inc(v_k_2439_);
                v___x_2451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_entries_2436_, v_h_2449_, v_depth_2432_, v_k_2439_, v_v_2440_);
                v_i_2435_ = v___x_2450_;
                v_entries_2436_ = v___x_2451_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_2455_: *mut LeanObject,
    mut v_keys_2456_: *mut LeanObject,
    mut v_vals_2457_: *mut LeanObject,
    mut v_i_2458_: *mut LeanObject,
    mut v_entries_2459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2460_: usize = 0;
    let mut v_res_2461_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2460_ = lean_unbox_usize(v_depth_2455_);
    lean_dec(v_depth_2455_);
    v_res_2461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_2460_, v_keys_2456_, v_vals_2457_, v_i_2458_, v_entries_2459_);
    lean_dec_ref(v_vals_2457_);
    lean_dec_ref(v_keys_2456_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2462_: *mut LeanObject,
    mut v_x_2463_: *mut LeanObject,
    mut v_x_2464_: *mut LeanObject,
    mut v_x_2465_: *mut LeanObject,
    mut v_x_2466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_887__boxed_2467_: usize = 0;
    let mut v_x_888__boxed_2468_: usize = 0;
    let mut v_res_2469_: *mut LeanObject = core::ptr::null_mut();
    v_x_887__boxed_2467_ = lean_unbox_usize(v_x_2463_);
    lean_dec(v_x_2463_);
    v_x_888__boxed_2468_ = lean_unbox_usize(v_x_2464_);
    lean_dec(v_x_2464_);
    v_res_2469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2462_, v_x_887__boxed_2467_, v_x_888__boxed_2468_, v_x_2465_, v_x_2466_);
    return v_res_2469_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_2470_: *mut LeanObject,
    mut v_x_2471_: *mut LeanObject,
    mut v_x_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2474_: u64 = 0;
    let mut v___x_2475_: usize = 0;
    let mut v___x_2476_: usize = 0;
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: u64 = 0;
    let mut v_hash_2479_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2471_) == 0 {
                    v___x_2478_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2474_ = v___x_2478_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2479_ = lean_ctor_get_uint64(
                        v_x_2471_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2474_ = v_hash_2479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2475_ = lean_uint64_to_usize(v___y_2474_);
                v___x_2476_ = 1usize;
                v___x_2477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2470_, v___x_2475_, v___x_2476_, v_x_2471_, v_x_2472_);
                return v___x_2477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_a_2480_: *mut LeanObject,
    mut v_x_2481_: *mut LeanObject,
) -> u8 {
    let mut v___x_2482_: u8 = 0;
    let mut v_key_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2481_) == 0 {
                    v___x_2482_ = 0;
                    return v___x_2482_;
                } else {
                    v_key_2483_ = lean_ctor_get(v_x_2481_, 0);
                    v_tail_2484_ = lean_ctor_get(v_x_2481_, 2);
                    v___x_2485_ = lean_name_eq(v_key_2483_, v_a_2480_);
                    if v___x_2485_ == 0 {
                        v_x_2481_ = v_tail_2484_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2485_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_2487_: *mut LeanObject,
    mut v_x_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2489_: u8 = 0;
    let mut v_r_2490_: *mut LeanObject = core::ptr::null_mut();
    v_res_2489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_2487_, v_x_2488_);
    lean_dec(v_x_2488_);
    lean_dec(v_a_2487_);
    v_r_2490_ = lean_box((v_res_2489_) as usize);
    return v_r_2490_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(
    mut v_a_2491_: *mut LeanObject,
    mut v_b_2492_: *mut LeanObject,
    mut v_x_2493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2500_: u8 = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2493_) == 0 {
                    lean_dec(v_b_2492_);
                    lean_dec(v_a_2491_);
                    return v_x_2493_;
                } else {
                    v_key_2494_ = lean_ctor_get(v_x_2493_, 0);
                    v_value_2495_ = lean_ctor_get(v_x_2493_, 1);
                    v_tail_2496_ = lean_ctor_get(v_x_2493_, 2);
                    v_isSharedCheck_2508_ = (!lean_is_exclusive(v_x_2493_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v___x_2498_ = v_x_2493_;
                        v_isShared_2499_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2496_);
                        lean_inc(v_value_2495_);
                        lean_inc(v_key_2494_);
                        lean_dec(v_x_2493_);
                        v___x_2498_ = lean_box(0);
                        v_isShared_2499_ = v_isSharedCheck_2508_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2500_ = lean_name_eq(v_key_2494_, v_a_2491_);
                if v___x_2500_ == 0 {
                    v___x_2501_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_a_2491_, v_b_2492_, v_tail_2496_);
                    if v_isShared_2499_ == 0 {
                        lean_ctor_set(v___x_2498_, 2, v___x_2501_);
                        v___x_2503_ = v___x_2498_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_key_2494_);
                        lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_value_2495_);
                        lean_ctor_set(v_reuseFailAlloc_2504_, 2, v___x_2501_);
                        v___x_2503_ = v_reuseFailAlloc_2504_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2495_);
                    lean_dec(v_key_2494_);
                    if v_isShared_2499_ == 0 {
                        lean_ctor_set(v___x_2498_, 1, v_b_2492_);
                        lean_ctor_set(v___x_2498_, 0, v_a_2491_);
                        v___x_2506_ = v___x_2498_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2491_);
                        lean_ctor_set(v_reuseFailAlloc_2507_, 1, v_b_2492_);
                        lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_tail_2496_);
                        v___x_2506_ = v_reuseFailAlloc_2507_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2503_;
            }
            3 => {
                return v___x_2506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9___redArg(
    mut v_x_2509_: *mut LeanObject,
    mut v_x_2510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: u64 = 0;
    let mut v___x_2520_: u64 = 0;
    let mut v___x_2521_: u64 = 0;
    let mut v_fold_2522_: u64 = 0;
    let mut v___x_2523_: u64 = 0;
    let mut v___x_2524_: u64 = 0;
    let mut v___x_2525_: u64 = 0;
    let mut v___x_2526_: usize = 0;
    let mut v___x_2527_: usize = 0;
    let mut v___x_2528_: usize = 0;
    let mut v___x_2529_: usize = 0;
    let mut v___x_2530_: usize = 0;
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: u64 = 0;
    let mut v_hash_2538_: u64 = 0;
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2510_) == 0 {
                    return v_x_2509_;
                } else {
                    v_key_2511_ = lean_ctor_get(v_x_2510_, 0);
                    v_value_2512_ = lean_ctor_get(v_x_2510_, 1);
                    v_tail_2513_ = lean_ctor_get(v_x_2510_, 2);
                    v_isSharedCheck_2539_ = (!lean_is_exclusive(v_x_2510_)) as u8;
                    if v_isSharedCheck_2539_ == 0 {
                        v___x_2515_ = v_x_2510_;
                        v_isShared_2516_ = v_isSharedCheck_2539_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2513_);
                        lean_inc(v_value_2512_);
                        lean_inc(v_key_2511_);
                        lean_dec(v_x_2510_);
                        v___x_2515_ = lean_box(0);
                        v_isShared_2516_ = v_isSharedCheck_2539_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2517_ = lean_array_get_size(v_x_2509_);
                if lean_obj_tag(v_key_2511_) == 0 {
                    v___x_2537_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2519_ = v___x_2537_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2538_ = lean_ctor_get_uint64(
                        v_key_2511_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2519_ = v_hash_2538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2520_ = 32u64;
                v___x_2521_ = lean_uint64_shift_right(v___y_2519_, v___x_2520_);
                v_fold_2522_ = lean_uint64_xor(v___y_2519_, v___x_2521_);
                v___x_2523_ = 16u64;
                v___x_2524_ = lean_uint64_shift_right(v_fold_2522_, v___x_2523_);
                v___x_2525_ = lean_uint64_xor(v_fold_2522_, v___x_2524_);
                v___x_2526_ = lean_uint64_to_usize(v___x_2525_);
                v___x_2527_ = lean_usize_of_nat(v___x_2517_);
                v___x_2528_ = 1usize;
                v___x_2529_ = lean_usize_sub(v___x_2527_, v___x_2528_);
                v___x_2530_ = lean_usize_land(v___x_2526_, v___x_2529_);
                v___x_2531_ = lean_array_uget_borrowed(v_x_2509_, v___x_2530_);
                lean_inc(v___x_2531_);
                if v_isShared_2516_ == 0 {
                    lean_ctor_set(v___x_2515_, 2, v___x_2531_);
                    v___x_2533_ = v___x_2515_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_key_2511_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_value_2512_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 2, v___x_2531_);
                    v___x_2533_ = v_reuseFailAlloc_2536_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2534_ = lean_array_uset(v_x_2509_, v___x_2530_, v___x_2533_);
                v_x_2509_ = v___x_2534_;
                v_x_2510_ = v_tail_2513_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7___redArg(
    mut v_i_2540_: *mut LeanObject,
    mut v_source_2541_: *mut LeanObject,
    mut v_target_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: u8 = 0;
    let mut v_es_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2543_ = lean_array_get_size(v_source_2541_);
                v___x_2544_ = lean_nat_dec_lt(v_i_2540_, v___x_2543_);
                if v___x_2544_ == 0 {
                    lean_dec_ref(v_source_2541_);
                    lean_dec(v_i_2540_);
                    return v_target_2542_;
                } else {
                    v_es_2545_ = lean_array_fget(v_source_2541_, v_i_2540_);
                    v___x_2546_ = lean_box(0);
                    v_source_2547_ = lean_array_fset(v_source_2541_, v_i_2540_, v___x_2546_);
                    v_target_2548_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_2542_, v_es_2545_);
                    v___x_2549_ = lean_unsigned_to_nat(1);
                    v___x_2550_ = lean_nat_add(v_i_2540_, v___x_2549_);
                    lean_dec(v_i_2540_);
                    v_i_2540_ = v___x_2550_;
                    v_source_2541_ = v_source_2547_;
                    v_target_2542_ = v_target_2548_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(
    mut v_data_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    v___x_2553_ = lean_array_get_size(v_data_2552_);
    v___x_2554_ = lean_unsigned_to_nat(2);
    v_nbuckets_2555_ = lean_nat_mul(v___x_2553_, v___x_2554_);
    v___x_2556_ = lean_unsigned_to_nat(0);
    v___x_2557_ = lean_box(0);
    v___x_2558_ = lean_mk_array(v_nbuckets_2555_, v___x_2557_);
    v___x_2559_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7___redArg(v___x_2556_, v_data_2552_, v___x_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_m_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
    mut v_b_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2570_: u64 = 0;
    let mut v___x_2571_: u64 = 0;
    let mut v___x_2572_: u64 = 0;
    let mut v_fold_2573_: u64 = 0;
    let mut v___x_2574_: u64 = 0;
    let mut v___x_2575_: u64 = 0;
    let mut v___x_2576_: u64 = 0;
    let mut v___x_2577_: usize = 0;
    let mut v___x_2578_: usize = 0;
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: usize = 0;
    let mut v___x_2581_: usize = 0;
    let mut v_bkt_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v_val_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u64 = 0;
    let mut v_hash_2609_: u64 = 0;
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2563_ = lean_ctor_get(v_m_2560_, 0);
                v_buckets_2564_ = lean_ctor_get(v_m_2560_, 1);
                v_isSharedCheck_2610_ = (!lean_is_exclusive(v_m_2560_)) as u8;
                if v_isSharedCheck_2610_ == 0 {
                    v___x_2566_ = v_m_2560_;
                    v_isShared_2567_ = v_isSharedCheck_2610_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2564_);
                    lean_inc(v_size_2563_);
                    lean_dec(v_m_2560_);
                    v___x_2566_ = lean_box(0);
                    v_isShared_2567_ = v_isSharedCheck_2610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2568_ = lean_array_get_size(v_buckets_2564_);
                if lean_obj_tag(v_a_2561_) == 0 {
                    v___x_2608_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2570_ = v___x_2608_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2609_ = lean_ctor_get_uint64(
                        v_a_2561_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2570_ = v_hash_2609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2571_ = 32u64;
                v___x_2572_ = lean_uint64_shift_right(v___y_2570_, v___x_2571_);
                v_fold_2573_ = lean_uint64_xor(v___y_2570_, v___x_2572_);
                v___x_2574_ = 16u64;
                v___x_2575_ = lean_uint64_shift_right(v_fold_2573_, v___x_2574_);
                v___x_2576_ = lean_uint64_xor(v_fold_2573_, v___x_2575_);
                v___x_2577_ = lean_uint64_to_usize(v___x_2576_);
                v___x_2578_ = lean_usize_of_nat(v___x_2568_);
                v___x_2579_ = 1usize;
                v___x_2580_ = lean_usize_sub(v___x_2578_, v___x_2579_);
                v___x_2581_ = lean_usize_land(v___x_2577_, v___x_2580_);
                v_bkt_2582_ = lean_array_uget_borrowed(v_buckets_2564_, v___x_2581_);
                v___x_2583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_2561_, v_bkt_2582_);
                if v___x_2583_ == 0 {
                    v___x_2584_ = lean_unsigned_to_nat(1);
                    v_size_x27_2585_ = lean_nat_add(v_size_2563_, v___x_2584_);
                    lean_dec(v_size_2563_);
                    lean_inc(v_bkt_2582_);
                    v___x_2586_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2586_, 0, v_a_2561_);
                    lean_ctor_set(v___x_2586_, 1, v_b_2562_);
                    lean_ctor_set(v___x_2586_, 2, v_bkt_2582_);
                    v_buckets_x27_2587_ =
                        lean_array_uset(v_buckets_2564_, v___x_2581_, v___x_2586_);
                    v___x_2588_ = lean_unsigned_to_nat(4);
                    v___x_2589_ = lean_nat_mul(v_size_x27_2585_, v___x_2588_);
                    v___x_2590_ = lean_unsigned_to_nat(3);
                    v___x_2591_ = lean_nat_div(v___x_2589_, v___x_2590_);
                    lean_dec(v___x_2589_);
                    v___x_2592_ = lean_array_get_size(v_buckets_x27_2587_);
                    v___x_2593_ = lean_nat_dec_le(v___x_2591_, v___x_2592_);
                    lean_dec(v___x_2591_);
                    if v___x_2593_ == 0 {
                        v_val_2594_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(v_buckets_x27_2587_);
                        if v_isShared_2567_ == 0 {
                            lean_ctor_set(v___x_2566_, 1, v_val_2594_);
                            lean_ctor_set(v___x_2566_, 0, v_size_x27_2585_);
                            v___x_2596_ = v___x_2566_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_size_x27_2585_);
                            lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_val_2594_);
                            v___x_2596_ = v_reuseFailAlloc_2597_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2567_ == 0 {
                            lean_ctor_set(v___x_2566_, 1, v_buckets_x27_2587_);
                            lean_ctor_set(v___x_2566_, 0, v_size_x27_2585_);
                            v___x_2599_ = v___x_2566_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_size_x27_2585_);
                            lean_ctor_set(v_reuseFailAlloc_2600_, 1, v_buckets_x27_2587_);
                            v___x_2599_ = v_reuseFailAlloc_2600_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2582_);
                    v___x_2601_ = lean_box(0);
                    v_buckets_x27_2602_ =
                        lean_array_uset(v_buckets_2564_, v___x_2581_, v___x_2601_);
                    v___x_2603_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_a_2561_, v_b_2562_, v_bkt_2582_);
                    v___x_2604_ = lean_array_uset(v_buckets_x27_2602_, v___x_2581_, v___x_2603_);
                    if v_isShared_2567_ == 0 {
                        lean_ctor_set(v___x_2566_, 1, v___x_2604_);
                        v___x_2606_ = v___x_2566_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_size_2563_);
                        lean_ctor_set(v_reuseFailAlloc_2607_, 1, v___x_2604_);
                        v___x_2606_ = v_reuseFailAlloc_2607_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2596_;
            }
            4 => {
                return v___x_2599_;
            }
            5 => {
                return v___x_2606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_2611_: *mut LeanObject,
    mut v_x_2612_: *mut LeanObject,
    mut v_x_2613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_2614_: u8 = 0;
    let mut v_map_u2081_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut v_map_u2081_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2614_ = lean_ctor_get_uint8(
                    v_x_2611_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2614_ == 0 {
                    v_map_u2081_2615_ = lean_ctor_get(v_x_2611_, 0);
                    v_map_u2082_2616_ = lean_ctor_get(v_x_2611_, 1);
                    v_isSharedCheck_2624_ = (!lean_is_exclusive(v_x_2611_)) as u8;
                    if v_isSharedCheck_2624_ == 0 {
                        v___x_2618_ = v_x_2611_;
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_2616_);
                        lean_inc(v_map_u2081_2615_);
                        lean_dec(v_x_2611_);
                        v___x_2618_ = lean_box(0);
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_2625_ = lean_ctor_get(v_x_2611_, 0);
                    v_map_u2082_2626_ = lean_ctor_get(v_x_2611_, 1);
                    v_isSharedCheck_2634_ = (!lean_is_exclusive(v_x_2611_)) as u8;
                    if v_isSharedCheck_2634_ == 0 {
                        v___x_2628_ = v_x_2611_;
                        v_isShared_2629_ = v_isSharedCheck_2634_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_2626_);
                        lean_inc(v_map_u2081_2625_);
                        lean_dec(v_x_2611_);
                        v___x_2628_ = lean_box(0);
                        v_isShared_2629_ = v_isSharedCheck_2634_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2620_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_u2082_2616_, v_x_2612_, v_x_2613_);
                if v_isShared_2619_ == 0 {
                    lean_ctor_set(v___x_2618_, 1, v___x_2620_);
                    v___x_2622_ = v___x_2618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_map_u2081_2615_);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2620_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2623_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_2614_,
                    );
                    v___x_2622_ = v_reuseFailAlloc_2623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2622_;
            }
            3 => {
                v___x_2630_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(v_map_u2081_2625_, v_x_2612_, v_x_2613_);
                if v_isShared_2629_ == 0 {
                    lean_ctor_set(v___x_2628_, 0, v___x_2630_);
                    v___x_2632_ = v___x_2628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 0, v___x_2630_);
                    lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_map_u2082_2626_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2633_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_2614_,
                    );
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_(
    mut v_x_2635_: *mut LeanObject,
    mut v_e_2636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmNames_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2641_: u8 = 0;
    let mut v_fromDeclName_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmName_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_2637_ = lean_ctor_get(v_x_2635_, 0);
                v_thmNames_2638_ = lean_ctor_get(v_x_2635_, 1);
                v_isSharedCheck_2650_ = (!lean_is_exclusive(v_x_2635_)) as u8;
                if v_isSharedCheck_2650_ == 0 {
                    v___x_2640_ = v_x_2635_;
                    v_isShared_2641_ = v_isSharedCheck_2650_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_thmNames_2638_);
                    lean_inc(v_map_2637_);
                    lean_dec(v_x_2635_);
                    v___x_2640_ = lean_box(0);
                    v_isShared_2641_ = v_isSharedCheck_2650_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fromDeclName_2642_ = lean_ctor_get(v_e_2636_, 0);
                lean_inc(v_fromDeclName_2642_);
                v_thmName_2643_ = lean_ctor_get(v_e_2636_, 2);
                lean_inc(v_thmName_2643_);
                v___x_2644_ = l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(v_map_2637_, v_fromDeclName_2642_, v_e_2636_);
                v___x_2645_ = lean_box(0);
                v___x_2646_ = l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(v_thmNames_2638_, v_thmName_2643_, v___x_2645_);
                if v_isShared_2641_ == 0 {
                    lean_ctor_set(v___x_2640_, 1, v___x_2646_);
                    lean_ctor_set(v___x_2640_, 0, v___x_2644_);
                    v___x_2648_ = v___x_2640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2644_);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2646_);
                    v___x_2648_ = v_reuseFailAlloc_2649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    v___f_2663_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__0_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___f_2664_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__1_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___x_2665_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5_once),
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default___closed__5,
    );
    v___f_2666_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__2_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___x_2667_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__7_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_;
    v___x_2668_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2668_, 0, v___x_2667_);
    lean_ctor_set(v___x_2668_, 1, v___f_2666_);
    lean_ctor_set(v___x_2668_, 2, v___x_2665_);
    lean_ctor_set(v___x_2668_, 3, v___f_2664_);
    lean_ctor_set(v___x_2668_, 4, v___f_2663_);
    return v___x_2668_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    v___x_2670_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__8_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_);
    v___x_2671_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_2670_);
    return v___x_2671_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2____boxed(
    mut v_a_2672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2673_: *mut LeanObject = core::ptr::null_mut();
    v_res_2673_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_();
    return v_res_2673_;
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_2674_: *mut LeanObject,
    mut v_x_2675_: *mut LeanObject,
    mut v_x_2676_: *mut LeanObject,
    mut v_x_2677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    v___x_2678_ = l_Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0___redArg(v_x_2675_, v_x_2676_, v_x_2677_);
    return v___x_2678_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_2679_: *mut LeanObject,
    mut v_x_2680_: *mut LeanObject,
    mut v_x_2681_: *mut LeanObject,
    mut v_x_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v___x_2683_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2680_, v_x_2681_, v_x_2682_);
    return v___x_2683_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_2684_: *mut LeanObject,
    mut v_m_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
    mut v_b_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    v___x_2688_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1___redArg(v_m_2685_, v_a_2686_, v_b_2687_);
    return v___x_2688_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_2689_: *mut LeanObject,
    mut v_x_2690_: *mut LeanObject,
    mut v_x_2691_: usize,
    mut v_x_2692_: usize,
    mut v_x_2693_: *mut LeanObject,
    mut v_x_2694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2690_, v_x_2691_, v_x_2692_, v_x_2693_, v_x_2694_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2696_: *mut LeanObject,
    mut v_x_2697_: *mut LeanObject,
    mut v_x_2698_: *mut LeanObject,
    mut v_x_2699_: *mut LeanObject,
    mut v_x_2700_: *mut LeanObject,
    mut v_x_2701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1461__boxed_2702_: usize = 0;
    let mut v_x_1462__boxed_2703_: usize = 0;
    let mut v_res_2704_: *mut LeanObject = core::ptr::null_mut();
    v_x_1461__boxed_2702_ = lean_unbox_usize(v_x_2698_);
    lean_dec(v_x_2698_);
    v_x_1462__boxed_2703_ = lean_unbox_usize(v_x_2699_);
    lean_dec(v_x_2699_);
    v_res_2704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2696_, v_x_2697_, v_x_1461__boxed_2702_, v_x_1462__boxed_2703_, v_x_2700_, v_x_2701_);
    return v_res_2704_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
    mut v_x_2707_: *mut LeanObject,
) -> u8 {
    let mut v___x_2708_: u8 = 0;
    v___x_2708_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_2706_, v_x_2707_);
    return v___x_2708_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2709_: *mut LeanObject,
    mut v_a_2710_: *mut LeanObject,
    mut v_x_2711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2712_: u8 = 0;
    let mut v_r_2713_: *mut LeanObject = core::ptr::null_mut();
    v_res_2712_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_2709_, v_a_2710_, v_x_2711_);
    lean_dec(v_x_2711_);
    lean_dec(v_a_2710_);
    v_r_2713_ = lean_box((v_res_2712_) as usize);
    return v_r_2713_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4(
    mut v_00_u03b2_2714_: *mut LeanObject,
    mut v_data_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    v___x_2716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4___redArg(v_data_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5(
    mut v_00_u03b2_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
    mut v_b_2719_: *mut LeanObject,
    mut v_x_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__5___redArg(v_a_2718_, v_b_2719_, v_x_2720_);
    return v___x_2721_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2722_: *mut LeanObject,
    mut v_n_2723_: *mut LeanObject,
    mut v_k_2724_: *mut LeanObject,
    mut v_v_2725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    v___x_2726_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_n_2723_, v_k_2724_, v_v_2725_);
    return v___x_2726_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2727_: *mut LeanObject,
    mut v_depth_2728_: usize,
    mut v_keys_2729_: *mut LeanObject,
    mut v_vals_2730_: *mut LeanObject,
    mut v_heq_2731_: *mut LeanObject,
    mut v_i_2732_: *mut LeanObject,
    mut v_entries_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    v___x_2734_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2728_, v_keys_2729_, v_vals_2730_, v_i_2732_, v_entries_2733_);
    return v___x_2734_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2735_: *mut LeanObject,
    mut v_depth_2736_: *mut LeanObject,
    mut v_keys_2737_: *mut LeanObject,
    mut v_vals_2738_: *mut LeanObject,
    mut v_heq_2739_: *mut LeanObject,
    mut v_i_2740_: *mut LeanObject,
    mut v_entries_2741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2742_: usize = 0;
    let mut v_res_2743_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2742_ = lean_unbox_usize(v_depth_2736_);
    lean_dec(v_depth_2736_);
    v_res_2743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2735_, v_depth_boxed_2742_, v_keys_2737_, v_vals_2738_, v_heq_2739_, v_i_2740_, v_entries_2741_);
    lean_dec_ref(v_vals_2738_);
    lean_dec_ref(v_keys_2737_);
    return v_res_2743_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_2744_: *mut LeanObject,
    mut v_i_2745_: *mut LeanObject,
    mut v_source_2746_: *mut LeanObject,
    mut v_target_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    v___x_2748_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7___redArg(v_i_2745_, v_source_2746_, v_target_2747_);
    return v___x_2748_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2749_: *mut LeanObject,
    mut v_x_2750_: *mut LeanObject,
    mut v_x_2751_: *mut LeanObject,
    mut v_x_2752_: *mut LeanObject,
    mut v_x_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    v___x_2754_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2750_, v_x_2751_, v_x_2752_, v_x_2753_);
    return v___x_2754_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v_00_u03b2_2755_: *mut LeanObject,
    mut v_x_2756_: *mut LeanObject,
    mut v_x_2757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    v___x_2758_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_2756_, v_x_2757_);
    return v___x_2758_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3(
    mut v_a_2762_: *mut LeanObject,
    mut v_a_2763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2762_) == 0 {
                    v___x_2764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2764_, 0, v_a_2763_);
                    return v___x_2764_;
                } else {
                    lean_dec_ref(v_a_2763_);
                    v_key_2765_ = lean_ctor_get(v_a_2762_, 0);
                    v_tail_2766_ = lean_ctor_get(v_a_2762_, 2);
                    v___x_2767_ = lean_box(0);
                    v___x_2768_ = l_Lean_Level_isParam(v_key_2765_);
                    if v___x_2768_ == 0 {
                        v___x_2769_ = lean_box((v___x_2768_) as usize);
                        v___x_2770_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2770_, 0, v___x_2769_);
                        v___x_2771_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2771_, 0, v___x_2770_);
                        lean_ctor_set(v___x_2771_, 1, v___x_2767_);
                        v___x_2772_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2772_, 0, v___x_2771_);
                        return v___x_2772_;
                    } else {
                        v___x_2773_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0;
                        v_a_2762_ = v_tail_2766_;
                        v_a_2763_ = v___x_2773_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___boxed(
    mut v_a_2775_: *mut LeanObject,
    mut v_a_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2777_: *mut LeanObject = core::ptr::null_mut();
    v_res_2777_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3(v_a_2775_, v_a_2776_);
    lean_dec(v_a_2775_);
    return v_res_2777_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4(
    mut v_as_2778_: *mut LeanObject,
    mut v_sz_2779_: usize,
    mut v_i_2780_: usize,
    mut v_b_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2782_: u8 = 0;
    let mut v_a_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: usize = 0;
    let mut v___x_2788_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2782_ = lean_usize_dec_lt(v_i_2780_, v_sz_2779_);
                if v___x_2782_ == 0 {
                    return v_b_2781_;
                } else {
                    v_a_2783_ = lean_array_uget_borrowed(v_as_2778_, v_i_2780_);
                    v___x_2784_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3(v_a_2783_, v_b_2781_);
                    if lean_obj_tag(v___x_2784_) == 0 {
                        v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
                        lean_inc(v_a_2785_);
                        lean_dec_ref_known(v___x_2784_, 1);
                        return v_a_2785_;
                    } else {
                        v_a_2786_ = lean_ctor_get(v___x_2784_, 0);
                        lean_inc(v_a_2786_);
                        lean_dec_ref_known(v___x_2784_, 1);
                        v___x_2787_ = 1usize;
                        v___x_2788_ = lean_usize_add(v_i_2780_, v___x_2787_);
                        v_i_2780_ = v___x_2788_;
                        v_b_2781_ = v_a_2786_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4___boxed(
    mut v_as_2790_: *mut LeanObject,
    mut v_sz_2791_: *mut LeanObject,
    mut v_i_2792_: *mut LeanObject,
    mut v_b_2793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2794_: usize = 0;
    let mut v_i_boxed_2795_: usize = 0;
    let mut v_res_2796_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2794_ = lean_unbox_usize(v_sz_2791_);
    lean_dec(v_sz_2791_);
    v_i_boxed_2795_ = lean_unbox_usize(v_i_2792_);
    lean_dec(v_i_2792_);
    v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4(v_as_2790_, v_sz_boxed_2794_, v_i_boxed_2795_, v_b_2793_);
    lean_dec_ref(v_as_2790_);
    return v_res_2796_;
}
pub unsafe fn l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1(
    mut v_x_2797_: *mut LeanObject,
    mut v_x_2798_: *mut LeanObject,
) -> u8 {
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: u8 = 0;
    let mut v_head_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2797_) == 0 {
                    if lean_obj_tag(v_x_2798_) == 0 {
                        v___x_2799_ = 1;
                        return v___x_2799_;
                    } else {
                        v___x_2800_ = 0;
                        return v___x_2800_;
                    }
                } else {
                    if lean_obj_tag(v_x_2798_) == 0 {
                        v___x_2801_ = 0;
                        return v___x_2801_;
                    } else {
                        v_head_2802_ = lean_ctor_get(v_x_2797_, 0);
                        v_tail_2803_ = lean_ctor_get(v_x_2797_, 1);
                        v_head_2804_ = lean_ctor_get(v_x_2798_, 0);
                        v_tail_2805_ = lean_ctor_get(v_x_2798_, 1);
                        v___x_2806_ = lean_level_eq(v_head_2802_, v_head_2804_);
                        if v___x_2806_ == 0 {
                            return v___x_2806_;
                        } else {
                            v_x_2797_ = v_tail_2803_;
                            v_x_2798_ = v_tail_2805_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1___boxed(
    mut v_x_2808_: *mut LeanObject,
    mut v_x_2809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2810_: u8 = 0;
    let mut v_r_2811_: *mut LeanObject = core::ptr::null_mut();
    v_res_2810_ = l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1(v_x_2808_, v_x_2809_);
    lean_dec(v_x_2809_);
    lean_dec(v_x_2808_);
    v_r_2811_ = lean_box((v_res_2810_) as usize);
    return v_r_2811_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    v___x_2812_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2812_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    v___x_2813_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__0);
    v___x_2814_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2814_, 0, v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    v___x_2815_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1);
    v___x_2816_ = lean_unsigned_to_nat(0);
    v___x_2817_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2817_, 0, v___x_2816_);
    lean_ctor_set(v___x_2817_, 1, v___x_2816_);
    lean_ctor_set(v___x_2817_, 2, v___x_2816_);
    lean_ctor_set(v___x_2817_, 3, v___x_2816_);
    lean_ctor_set(v___x_2817_, 4, v___x_2815_);
    lean_ctor_set(v___x_2817_, 5, v___x_2815_);
    lean_ctor_set(v___x_2817_, 6, v___x_2815_);
    lean_ctor_set(v___x_2817_, 7, v___x_2815_);
    lean_ctor_set(v___x_2817_, 8, v___x_2815_);
    lean_ctor_set(v___x_2817_, 9, v___x_2815_);
    return v___x_2817_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    v___x_2818_ = lean_unsigned_to_nat(32);
    v___x_2819_ = lean_mk_empty_array_with_capacity(v___x_2818_);
    v___x_2820_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2820_, 0, v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2821_: usize = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    v___x_2821_ = 5usize;
    v___x_2822_ = lean_unsigned_to_nat(0);
    v___x_2823_ = lean_unsigned_to_nat(32);
    v___x_2824_ = lean_mk_empty_array_with_capacity(v___x_2823_);
    v___x_2825_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__3);
    v___x_2826_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2826_, 0, v___x_2825_);
    lean_ctor_set(v___x_2826_, 1, v___x_2824_);
    lean_ctor_set(v___x_2826_, 2, v___x_2822_);
    lean_ctor_set(v___x_2826_, 3, v___x_2822_);
    lean_ctor_set_usize(v___x_2826_, 4, v___x_2821_);
    return v___x_2826_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    v___x_2827_ = lean_box(1);
    v___x_2828_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__4);
    v___x_2829_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__1);
    v___x_2830_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2830_, 0, v___x_2829_);
    lean_ctor_set(v___x_2830_, 1, v___x_2828_);
    lean_ctor_set(v___x_2830_, 2, v___x_2827_);
    return v___x_2830_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    v___x_2832_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__6;
    v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
    return v___x_2833_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__8;
    v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
    return v___x_2836_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    v___x_2838_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__10;
    v___x_2839_ = l_Lean_stringToMessageData(v___x_2838_);
    return v___x_2839_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    v___x_2841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__12;
    v___x_2842_ = l_Lean_stringToMessageData(v___x_2841_);
    return v___x_2842_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__14;
    v___x_2845_ = l_Lean_stringToMessageData(v___x_2844_);
    return v___x_2845_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    v___x_2847_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__16;
    v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
    return v___x_2848_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    v___x_2850_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__18;
    v___x_2851_ = l_Lean_stringToMessageData(v___x_2850_);
    return v___x_2851_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(
    mut v_msg_2852_: *mut LeanObject,
    mut v_declHint_2853_: *mut LeanObject,
    mut v___y_2854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: u8 = 0;
    let mut v_isExporting_2859_: u8 = 0;
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2856_ = lean_st_ref_get(v___y_2854_);
                v_env_2857_ = lean_ctor_get(v___x_2856_, 0);
                lean_inc_ref(v_env_2857_);
                lean_dec(v___x_2856_);
                v___x_2858_ = l_Lean_Name_isAnonymous(v_declHint_2853_);
                if v___x_2858_ == 0 {
                    v_isExporting_2859_ = lean_ctor_get_uint8(
                        v_env_2857_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2859_ == 0 {
                        lean_dec_ref(v_env_2857_);
                        lean_dec(v_declHint_2853_);
                        v___x_2860_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2860_, 0, v_msg_2852_);
                        return v___x_2860_;
                    } else {
                        lean_inc_ref(v_env_2857_);
                        v___x_2861_ = l_Lean_Environment_setExporting(v_env_2857_, v___x_2858_);
                        lean_inc(v_declHint_2853_);
                        lean_inc_ref(v___x_2861_);
                        v___x_2862_ = l_Lean_Environment_contains(
                            v___x_2861_,
                            v_declHint_2853_,
                            v_isExporting_2859_,
                        );
                        if v___x_2862_ == 0 {
                            lean_dec_ref(v___x_2861_);
                            lean_dec_ref(v_env_2857_);
                            lean_dec(v_declHint_2853_);
                            v___x_2863_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2863_, 0, v_msg_2852_);
                            return v___x_2863_;
                        } else {
                            v___x_2864_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2);
                            v___x_2865_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5);
                            v___x_2866_ = l_Lean_Options_empty;
                            v___x_2867_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2867_, 0, v___x_2861_);
                            lean_ctor_set(v___x_2867_, 1, v___x_2864_);
                            lean_ctor_set(v___x_2867_, 2, v___x_2865_);
                            lean_ctor_set(v___x_2867_, 3, v___x_2866_);
                            lean_inc(v_declHint_2853_);
                            v___x_2868_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2853_, v___x_2858_);
                            v_c_2869_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2869_, 0, v___x_2867_);
                            lean_ctor_set(v_c_2869_, 1, v___x_2868_);
                            v___x_2870_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2857_,
                                v_declHint_2853_,
                            );
                            if lean_obj_tag(v___x_2870_) == 0 {
                                lean_dec_ref(v_env_2857_);
                                lean_dec(v_declHint_2853_);
                                v___x_2871_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7);
                                v___x_2872_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2872_, 0, v___x_2871_);
                                lean_ctor_set(v___x_2872_, 1, v_c_2869_);
                                v___x_2873_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__9);
                                v___x_2874_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2874_, 0, v___x_2872_);
                                lean_ctor_set(v___x_2874_, 1, v___x_2873_);
                                v___x_2875_ = l_Lean_MessageData_note(v___x_2874_);
                                v___x_2876_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2876_, 0, v_msg_2852_);
                                lean_ctor_set(v___x_2876_, 1, v___x_2875_);
                                v___x_2877_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2877_, 0, v___x_2876_);
                                return v___x_2877_;
                            } else {
                                v_val_2878_ = lean_ctor_get(v___x_2870_, 0);
                                v_isSharedCheck_2913_ = (!lean_is_exclusive(v___x_2870_)) as u8;
                                if v_isSharedCheck_2913_ == 0 {
                                    v___x_2880_ = v___x_2870_;
                                    v_isShared_2881_ = v_isSharedCheck_2913_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2878_);
                                    lean_dec(v___x_2870_);
                                    v___x_2880_ = lean_box(0);
                                    v_isShared_2881_ = v_isSharedCheck_2913_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2857_);
                    lean_dec(v_declHint_2853_);
                    v___x_2914_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2914_, 0, v_msg_2852_);
                    return v___x_2914_;
                }
            }
            1 => {
                v___x_2882_ = lean_box(0);
                v___x_2883_ = l_Lean_Environment_header(v_env_2857_);
                lean_dec_ref(v_env_2857_);
                v___x_2884_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2883_);
                v_mod_2885_ = lean_array_get(v___x_2882_, v___x_2884_, v_val_2878_);
                lean_dec(v_val_2878_);
                lean_dec_ref(v___x_2884_);
                v___x_2886_ = l_Lean_isPrivateName(v_declHint_2853_);
                lean_dec(v_declHint_2853_);
                if v___x_2886_ == 0 {
                    v___x_2887_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__11);
                    v___x_2888_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2888_, 0, v___x_2887_);
                    lean_ctor_set(v___x_2888_, 1, v_c_2869_);
                    v___x_2889_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__13);
                    v___x_2890_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2890_, 0, v___x_2888_);
                    lean_ctor_set(v___x_2890_, 1, v___x_2889_);
                    v___x_2891_ = l_Lean_MessageData_ofName(v_mod_2885_);
                    v___x_2892_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2892_, 0, v___x_2890_);
                    lean_ctor_set(v___x_2892_, 1, v___x_2891_);
                    v___x_2893_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__15);
                    v___x_2894_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2894_, 0, v___x_2892_);
                    lean_ctor_set(v___x_2894_, 1, v___x_2893_);
                    v___x_2895_ = l_Lean_MessageData_note(v___x_2894_);
                    v___x_2896_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2896_, 0, v_msg_2852_);
                    lean_ctor_set(v___x_2896_, 1, v___x_2895_);
                    if v_isShared_2881_ == 0 {
                        lean_ctor_set_tag(v___x_2880_, 0);
                        lean_ctor_set(v___x_2880_, 0, v___x_2896_);
                        v___x_2898_ = v___x_2880_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
                        v___x_2898_ = v_reuseFailAlloc_2899_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2900_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__7);
                    v___x_2901_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2901_, 0, v___x_2900_);
                    lean_ctor_set(v___x_2901_, 1, v_c_2869_);
                    v___x_2902_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__17);
                    v___x_2903_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2903_, 0, v___x_2901_);
                    lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                    v___x_2904_ = l_Lean_MessageData_ofName(v_mod_2885_);
                    v___x_2905_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2905_, 0, v___x_2903_);
                    lean_ctor_set(v___x_2905_, 1, v___x_2904_);
                    v___x_2906_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__19);
                    v___x_2907_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2907_, 0, v___x_2905_);
                    lean_ctor_set(v___x_2907_, 1, v___x_2906_);
                    v___x_2908_ = l_Lean_MessageData_note(v___x_2907_);
                    v___x_2909_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2909_, 0, v_msg_2852_);
                    lean_ctor_set(v___x_2909_, 1, v___x_2908_);
                    if v_isShared_2881_ == 0 {
                        lean_ctor_set_tag(v___x_2880_, 0);
                        lean_ctor_set(v___x_2880_, 0, v___x_2909_);
                        v___x_2911_ = v___x_2880_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
                        v___x_2911_ = v_reuseFailAlloc_2912_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2898_;
            }
            3 => {
                return v___x_2911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___boxed(
    mut v_msg_2915_: *mut LeanObject,
    mut v_declHint_2916_: *mut LeanObject,
    mut v___y_2917_: *mut LeanObject,
    mut v___y_2918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2919_: *mut LeanObject = core::ptr::null_mut();
    v_res_2919_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(v_msg_2915_, v_declHint_2916_, v___y_2917_);
    lean_dec(v___y_2917_);
    return v_res_2919_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9(
    mut v_msg_2920_: *mut LeanObject,
    mut v_declHint_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2925_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(v_msg_2920_, v_declHint_2921_, v___y_2923_);
                v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
                v_isSharedCheck_2935_ = (!lean_is_exclusive(v___x_2925_)) as u8;
                if v_isSharedCheck_2935_ == 0 {
                    v___x_2928_ = v___x_2925_;
                    v_isShared_2929_ = v_isSharedCheck_2935_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2926_);
                    lean_dec(v___x_2925_);
                    v___x_2928_ = lean_box(0);
                    v_isShared_2929_ = v_isSharedCheck_2935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2930_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2931_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2931_, 0, v___x_2930_);
                lean_ctor_set(v___x_2931_, 1, v_a_2926_);
                if v_isShared_2929_ == 0 {
                    lean_ctor_set(v___x_2928_, 0, v___x_2931_);
                    v___x_2933_ = v___x_2928_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(
    mut v_msg_2936_: *mut LeanObject,
    mut v_declHint_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
    mut v___y_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2941_: *mut LeanObject = core::ptr::null_mut();
    v_res_2941_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9(v_msg_2936_, v_declHint_2937_, v___y_2938_, v___y_2939_);
    lean_dec(v___y_2939_);
    lean_dec_ref(v___y_2938_);
    return v_res_2941_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(
    mut v_msgData_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    v___x_2946_ = lean_st_ref_get(v___y_2944_);
    v_env_2947_ = lean_ctor_get(v___x_2946_, 0);
    lean_inc_ref(v_env_2947_);
    lean_dec(v___x_2946_);
    v_options_2948_ = lean_ctor_get(v___y_2943_, 2);
    v___x_2949_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__2);
    v___x_2950_ = lean_unsigned_to_nat(32);
    v___x_2951_ = lean_mk_empty_array_with_capacity(v___x_2950_);
    lean_dec_ref(v___x_2951_);
    v___x_2952_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg___closed__5);
    lean_inc_ref(v_options_2948_);
    v___x_2953_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2953_, 0, v_env_2947_);
    lean_ctor_set(v___x_2953_, 1, v___x_2949_);
    lean_ctor_set(v___x_2953_, 2, v___x_2952_);
    lean_ctor_set(v___x_2953_, 3, v_options_2948_);
    v___x_2954_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2954_, 0, v___x_2953_);
    lean_ctor_set(v___x_2954_, 1, v_msgData_2942_);
    v___x_2955_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2955_, 0, v___x_2954_);
    return v___x_2955_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16___boxed(
    mut v_msgData_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2960_: *mut LeanObject = core::ptr::null_mut();
    v_res_2960_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v_msgData_2956_, v___y_2957_, v___y_2958_);
    lean_dec(v___y_2958_);
    lean_dec_ref(v___y_2957_);
    return v_res_2960_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(
    mut v_msg_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2970_: u8 = 0;
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2965_ = lean_ctor_get(v___y_2962_, 5);
                v___x_2966_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v_msg_2961_, v___y_2962_, v___y_2963_);
                v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
                v_isSharedCheck_2975_ = (!lean_is_exclusive(v___x_2966_)) as u8;
                if v_isSharedCheck_2975_ == 0 {
                    v___x_2969_ = v___x_2966_;
                    v_isShared_2970_ = v_isSharedCheck_2975_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2967_);
                    lean_dec(v___x_2966_);
                    v___x_2969_ = lean_box(0);
                    v_isShared_2970_ = v_isSharedCheck_2975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2965_);
                v___x_2971_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2971_, 0, v_ref_2965_);
                lean_ctor_set(v___x_2971_, 1, v_a_2967_);
                if v_isShared_2970_ == 0 {
                    lean_ctor_set_tag(v___x_2969_, 1);
                    lean_ctor_set(v___x_2969_, 0, v___x_2971_);
                    v___x_2973_ = v___x_2969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2974_, 0, v___x_2971_);
                    v___x_2973_ = v_reuseFailAlloc_2974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg___boxed(
    mut v_msg_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
    mut v___y_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2980_: *mut LeanObject = core::ptr::null_mut();
    v_res_2980_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v_msg_2976_, v___y_2977_, v___y_2978_);
    lean_dec(v___y_2978_);
    lean_dec_ref(v___y_2977_);
    return v_res_2980_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(
    mut v_ref_2981_: *mut LeanObject,
    mut v_msg_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2998_: u8 = 0;
    let mut v_cancelTk_x3f_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3000_: u8 = 0;
    let mut v_inheritedTraceOptions_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2986_ = lean_ctor_get(v___y_2983_, 0);
    v_fileMap_2987_ = lean_ctor_get(v___y_2983_, 1);
    v_options_2988_ = lean_ctor_get(v___y_2983_, 2);
    v_currRecDepth_2989_ = lean_ctor_get(v___y_2983_, 3);
    v_maxRecDepth_2990_ = lean_ctor_get(v___y_2983_, 4);
    v_ref_2991_ = lean_ctor_get(v___y_2983_, 5);
    v_currNamespace_2992_ = lean_ctor_get(v___y_2983_, 6);
    v_openDecls_2993_ = lean_ctor_get(v___y_2983_, 7);
    v_initHeartbeats_2994_ = lean_ctor_get(v___y_2983_, 8);
    v_maxHeartbeats_2995_ = lean_ctor_get(v___y_2983_, 9);
    v_quotContext_2996_ = lean_ctor_get(v___y_2983_, 10);
    v_currMacroScope_2997_ = lean_ctor_get(v___y_2983_, 11);
    v_diag_2998_ = lean_ctor_get_uint8(
        v___y_2983_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2999_ = lean_ctor_get(v___y_2983_, 12);
    v_suppressElabErrors_3000_ = lean_ctor_get_uint8(
        v___y_2983_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3001_ = lean_ctor_get(v___y_2983_, 13);
    v_ref_3002_ = l_Lean_replaceRef(v_ref_2981_, v_ref_2991_);
    lean_inc_ref(v_inheritedTraceOptions_3001_);
    lean_inc(v_cancelTk_x3f_2999_);
    lean_inc(v_currMacroScope_2997_);
    lean_inc(v_quotContext_2996_);
    lean_inc(v_maxHeartbeats_2995_);
    lean_inc(v_initHeartbeats_2994_);
    lean_inc(v_openDecls_2993_);
    lean_inc(v_currNamespace_2992_);
    lean_inc(v_maxRecDepth_2990_);
    lean_inc(v_currRecDepth_2989_);
    lean_inc_ref(v_options_2988_);
    lean_inc_ref(v_fileMap_2987_);
    lean_inc_ref(v_fileName_2986_);
    v___x_3003_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3003_, 0, v_fileName_2986_);
    lean_ctor_set(v___x_3003_, 1, v_fileMap_2987_);
    lean_ctor_set(v___x_3003_, 2, v_options_2988_);
    lean_ctor_set(v___x_3003_, 3, v_currRecDepth_2989_);
    lean_ctor_set(v___x_3003_, 4, v_maxRecDepth_2990_);
    lean_ctor_set(v___x_3003_, 5, v_ref_3002_);
    lean_ctor_set(v___x_3003_, 6, v_currNamespace_2992_);
    lean_ctor_set(v___x_3003_, 7, v_openDecls_2993_);
    lean_ctor_set(v___x_3003_, 8, v_initHeartbeats_2994_);
    lean_ctor_set(v___x_3003_, 9, v_maxHeartbeats_2995_);
    lean_ctor_set(v___x_3003_, 10, v_quotContext_2996_);
    lean_ctor_set(v___x_3003_, 11, v_currMacroScope_2997_);
    lean_ctor_set(v___x_3003_, 12, v_cancelTk_x3f_2999_);
    lean_ctor_set(v___x_3003_, 13, v_inheritedTraceOptions_3001_);
    lean_ctor_set_uint8(
        v___x_3003_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2998_,
    );
    lean_ctor_set_uint8(
        v___x_3003_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3000_,
    );
    v___x_3004_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v_msg_2982_, v___x_3003_, v___y_2984_);
    lean_dec_ref_known(v___x_3003_, 14);
    return v___x_3004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg___boxed(
    mut v_ref_3005_: *mut LeanObject,
    mut v_msg_3006_: *mut LeanObject,
    mut v___y_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3010_: *mut LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_ref_3005_, v_msg_3006_, v___y_3007_, v___y_3008_);
    lean_dec(v___y_3008_);
    lean_dec_ref(v___y_3007_);
    lean_dec(v_ref_3005_);
    return v_res_3010_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_ref_3011_: *mut LeanObject,
    mut v_msg_3012_: *mut LeanObject,
    mut v_declHint_3013_: *mut LeanObject,
    mut v___y_3014_: *mut LeanObject,
    mut v___y_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    v___x_3017_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9(v_msg_3012_, v_declHint_3013_, v___y_3014_, v___y_3015_);
    v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
    lean_inc(v_a_3018_);
    lean_dec_ref(v___x_3017_);
    v___x_3019_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_ref_3011_, v_a_3018_, v___y_3014_, v___y_3015_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_ref_3020_: *mut LeanObject,
    mut v_msg_3021_: *mut LeanObject,
    mut v_declHint_3022_: *mut LeanObject,
    mut v___y_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
    mut v___y_3025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3026_: *mut LeanObject = core::ptr::null_mut();
    v_res_3026_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_3020_, v_msg_3021_, v_declHint_3022_, v___y_3023_, v___y_3024_);
    lean_dec(v___y_3024_);
    lean_dec_ref(v___y_3023_);
    lean_dec(v_ref_3020_);
    return v_res_3026_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    v___x_3028_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_3029_ = l_Lean_stringToMessageData(v___x_3028_);
    return v___x_3029_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    v___x_3031_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_3032_ = l_Lean_stringToMessageData(v___x_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_3033_: *mut LeanObject,
    mut v_constName_3034_: *mut LeanObject,
    mut v___y_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    v___x_3038_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_3039_ = 0;
    lean_inc(v_constName_3034_);
    v___x_3040_ = l_Lean_MessageData_ofConstName(v_constName_3034_, v___x_3039_);
    v___x_3041_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3041_, 0, v___x_3038_);
    lean_ctor_set(v___x_3041_, 1, v___x_3040_);
    v___x_3042_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_3043_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3043_, 0, v___x_3041_);
    lean_ctor_set(v___x_3043_, 1, v___x_3042_);
    v___x_3044_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_3033_, v___x_3043_, v_constName_3034_, v___y_3035_, v___y_3036_);
    return v___x_3044_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_3045_: *mut LeanObject,
    mut v_constName_3046_: *mut LeanObject,
    mut v___y_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3050_: *mut LeanObject = core::ptr::null_mut();
    v_res_3050_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(v_ref_3045_, v_constName_3046_, v___y_3047_, v___y_3048_);
    lean_dec(v___y_3048_);
    lean_dec_ref(v___y_3047_);
    lean_dec(v_ref_3045_);
    return v_res_3050_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(
    mut v_constName_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
    mut v___y_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3055_ = lean_ctor_get(v___y_3052_, 5);
    v___x_3056_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(v_ref_3055_, v_constName_3051_, v___y_3052_, v___y_3053_);
    return v___x_3056_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v___y_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3061_: *mut LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(v_constName_3057_, v___y_3058_, v___y_3059_);
    lean_dec(v___y_3059_);
    lean_dec_ref(v___y_3058_);
    return v_res_3061_;
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(
    mut v_constName_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3074_: u8 = 0;
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3066_ = lean_st_ref_get(v___y_3064_);
                v_env_3067_ = lean_ctor_get(v___x_3066_, 0);
                lean_inc_ref(v_env_3067_);
                lean_dec(v___x_3066_);
                v___x_3068_ = 0;
                lean_inc(v_constName_3062_);
                v___x_3069_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_3067_,
                    v_constName_3062_,
                    v___x_3068_,
                );
                if lean_obj_tag(v___x_3069_) == 0 {
                    v___x_3070_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(v_constName_3062_, v___y_3063_, v___y_3064_);
                    return v___x_3070_;
                } else {
                    lean_dec(v_constName_3062_);
                    v_val_3071_ = lean_ctor_get(v___x_3069_, 0);
                    v_isSharedCheck_3078_ = (!lean_is_exclusive(v___x_3069_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v___x_3073_ = v___x_3069_;
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3071_);
                        lean_dec(v___x_3069_);
                        v___x_3073_ = lean_box(0);
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3074_ == 0 {
                    lean_ctor_set_tag(v___x_3073_, 0);
                    v___x_3076_ = v___x_3073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_val_3071_);
                    v___x_3076_ = v_reuseFailAlloc_3077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0___boxed(
    mut v_constName_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
    mut v___y_3081_: *mut LeanObject,
    mut v___y_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3083_: *mut LeanObject = core::ptr::null_mut();
    v_res_3083_ = l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(v_constName_3079_, v___y_3080_, v___y_3081_);
    lean_dec(v___y_3081_);
    lean_dec_ref(v___y_3080_);
    return v_res_3083_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14___redArg(
    mut v_x_3084_: *mut LeanObject,
    mut v_x_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3091_: u8 = 0;
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: u64 = 0;
    let mut v___x_3094_: u64 = 0;
    let mut v___x_3095_: u64 = 0;
    let mut v_fold_3096_: u64 = 0;
    let mut v___x_3097_: u64 = 0;
    let mut v___x_3098_: u64 = 0;
    let mut v___x_3099_: u64 = 0;
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: usize = 0;
    let mut v___x_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3085_) == 0 {
                    return v_x_3084_;
                } else {
                    v_key_3086_ = lean_ctor_get(v_x_3085_, 0);
                    v_value_3087_ = lean_ctor_get(v_x_3085_, 1);
                    v_tail_3088_ = lean_ctor_get(v_x_3085_, 2);
                    v_isSharedCheck_3111_ = (!lean_is_exclusive(v_x_3085_)) as u8;
                    if v_isSharedCheck_3111_ == 0 {
                        v___x_3090_ = v_x_3085_;
                        v_isShared_3091_ = v_isSharedCheck_3111_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3088_);
                        lean_inc(v_value_3087_);
                        lean_inc(v_key_3086_);
                        lean_dec(v_x_3085_);
                        v___x_3090_ = lean_box(0);
                        v_isShared_3091_ = v_isSharedCheck_3111_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3092_ = lean_array_get_size(v_x_3084_);
                v___x_3093_ = l_Lean_Level_hash(v_key_3086_);
                v___x_3094_ = 32u64;
                v___x_3095_ = lean_uint64_shift_right(v___x_3093_, v___x_3094_);
                v_fold_3096_ = lean_uint64_xor(v___x_3093_, v___x_3095_);
                v___x_3097_ = 16u64;
                v___x_3098_ = lean_uint64_shift_right(v_fold_3096_, v___x_3097_);
                v___x_3099_ = lean_uint64_xor(v_fold_3096_, v___x_3098_);
                v___x_3100_ = lean_uint64_to_usize(v___x_3099_);
                v___x_3101_ = lean_usize_of_nat(v___x_3092_);
                v___x_3102_ = 1usize;
                v___x_3103_ = lean_usize_sub(v___x_3101_, v___x_3102_);
                v___x_3104_ = lean_usize_land(v___x_3100_, v___x_3103_);
                v___x_3105_ = lean_array_uget_borrowed(v_x_3084_, v___x_3104_);
                lean_inc(v___x_3105_);
                if v_isShared_3091_ == 0 {
                    lean_ctor_set(v___x_3090_, 2, v___x_3105_);
                    v___x_3107_ = v___x_3090_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_key_3086_);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_value_3087_);
                    lean_ctor_set(v_reuseFailAlloc_3110_, 2, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3110_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3108_ = lean_array_uset(v_x_3084_, v___x_3104_, v___x_3107_);
                v_x_3084_ = v___x_3108_;
                v_x_3085_ = v_tail_3088_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10___redArg(
    mut v_i_3112_: *mut LeanObject,
    mut v_source_3113_: *mut LeanObject,
    mut v_target_3114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: u8 = 0;
    let mut v_es_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3115_ = lean_array_get_size(v_source_3113_);
                v___x_3116_ = lean_nat_dec_lt(v_i_3112_, v___x_3115_);
                if v___x_3116_ == 0 {
                    lean_dec_ref(v_source_3113_);
                    lean_dec(v_i_3112_);
                    return v_target_3114_;
                } else {
                    v_es_3117_ = lean_array_fget(v_source_3113_, v_i_3112_);
                    v___x_3118_ = lean_box(0);
                    v_source_3119_ = lean_array_fset(v_source_3113_, v_i_3112_, v___x_3118_);
                    v_target_3120_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14___redArg(v_target_3114_, v_es_3117_);
                    v___x_3121_ = lean_unsigned_to_nat(1);
                    v___x_3122_ = lean_nat_add(v_i_3112_, v___x_3121_);
                    lean_dec(v_i_3112_);
                    v_i_3112_ = v___x_3122_;
                    v_source_3113_ = v_source_3119_;
                    v_target_3114_ = v_target_3120_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6___redArg(
    mut v_data_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    v___x_3125_ = lean_array_get_size(v_data_3124_);
    v___x_3126_ = lean_unsigned_to_nat(2);
    v_nbuckets_3127_ = lean_nat_mul(v___x_3125_, v___x_3126_);
    v___x_3128_ = lean_unsigned_to_nat(0);
    v___x_3129_ = lean_box(0);
    v___x_3130_ = lean_mk_array(v_nbuckets_3127_, v___x_3129_);
    v___x_3131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10___redArg(v___x_3128_, v_data_3124_, v___x_3130_);
    return v___x_3131_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(
    mut v_a_3132_: *mut LeanObject,
    mut v_x_3133_: *mut LeanObject,
) -> u8 {
    let mut v___x_3134_: u8 = 0;
    let mut v_key_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3133_) == 0 {
                    v___x_3134_ = 0;
                    return v___x_3134_;
                } else {
                    v_key_3135_ = lean_ctor_get(v_x_3133_, 0);
                    v_tail_3136_ = lean_ctor_get(v_x_3133_, 2);
                    v___x_3137_ = lean_level_eq(v_key_3135_, v_a_3132_);
                    if v___x_3137_ == 0 {
                        v_x_3133_ = v_tail_3136_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3137_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_a_3139_: *mut LeanObject,
    mut v_x_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3141_: u8 = 0;
    let mut v_r_3142_: *mut LeanObject = core::ptr::null_mut();
    v_res_3141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(v_a_3139_, v_x_3140_);
    lean_dec(v_x_3140_);
    lean_dec(v_a_3139_);
    v_r_3142_ = lean_box((v_res_3141_) as usize);
    return v_r_3142_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3___redArg(
    mut v_m_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_b_3145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: u64 = 0;
    let mut v___x_3150_: u64 = 0;
    let mut v___x_3151_: u64 = 0;
    let mut v_fold_3152_: u64 = 0;
    let mut v___x_3153_: u64 = 0;
    let mut v___x_3154_: u64 = 0;
    let mut v___x_3155_: u64 = 0;
    let mut v___x_3156_: usize = 0;
    let mut v___x_3157_: usize = 0;
    let mut v___x_3158_: usize = 0;
    let mut v___x_3159_: usize = 0;
    let mut v___x_3160_: usize = 0;
    let mut v_bkt_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: u8 = 0;
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v_val_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_unused_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3146_ = lean_ctor_get(v_m_3143_, 0);
                v_buckets_3147_ = lean_ctor_get(v_m_3143_, 1);
                v___x_3148_ = lean_array_get_size(v_buckets_3147_);
                v___x_3149_ = l_Lean_Level_hash(v_a_3144_);
                v___x_3150_ = 32u64;
                v___x_3151_ = lean_uint64_shift_right(v___x_3149_, v___x_3150_);
                v_fold_3152_ = lean_uint64_xor(v___x_3149_, v___x_3151_);
                v___x_3153_ = 16u64;
                v___x_3154_ = lean_uint64_shift_right(v_fold_3152_, v___x_3153_);
                v___x_3155_ = lean_uint64_xor(v_fold_3152_, v___x_3154_);
                v___x_3156_ = lean_uint64_to_usize(v___x_3155_);
                v___x_3157_ = lean_usize_of_nat(v___x_3148_);
                v___x_3158_ = 1usize;
                v___x_3159_ = lean_usize_sub(v___x_3157_, v___x_3158_);
                v___x_3160_ = lean_usize_land(v___x_3156_, v___x_3159_);
                v_bkt_3161_ = lean_array_uget_borrowed(v_buckets_3147_, v___x_3160_);
                v___x_3162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(v_a_3144_, v_bkt_3161_);
                if v___x_3162_ == 0 {
                    lean_inc_ref(v_buckets_3147_);
                    lean_inc(v_size_3146_);
                    v_isSharedCheck_3183_ = (!lean_is_exclusive(v_m_3143_)) as u8;
                    if v_isSharedCheck_3183_ == 0 {
                        v_unused_3184_ = lean_ctor_get(v_m_3143_, 1);
                        lean_dec(v_unused_3184_);
                        v_unused_3185_ = lean_ctor_get(v_m_3143_, 0);
                        lean_dec(v_unused_3185_);
                        v___x_3164_ = v_m_3143_;
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_3143_);
                        v___x_3164_ = lean_box(0);
                        v_isShared_3165_ = v_isSharedCheck_3183_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_3145_);
                    lean_dec(v_a_3144_);
                    return v_m_3143_;
                }
            }
            1 => {
                v___x_3166_ = lean_unsigned_to_nat(1);
                v_size_x27_3167_ = lean_nat_add(v_size_3146_, v___x_3166_);
                lean_dec(v_size_3146_);
                lean_inc(v_bkt_3161_);
                v___x_3168_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3168_, 0, v_a_3144_);
                lean_ctor_set(v___x_3168_, 1, v_b_3145_);
                lean_ctor_set(v___x_3168_, 2, v_bkt_3161_);
                v_buckets_x27_3169_ = lean_array_uset(v_buckets_3147_, v___x_3160_, v___x_3168_);
                v___x_3170_ = lean_unsigned_to_nat(4);
                v___x_3171_ = lean_nat_mul(v_size_x27_3167_, v___x_3170_);
                v___x_3172_ = lean_unsigned_to_nat(3);
                v___x_3173_ = lean_nat_div(v___x_3171_, v___x_3172_);
                lean_dec(v___x_3171_);
                v___x_3174_ = lean_array_get_size(v_buckets_x27_3169_);
                v___x_3175_ = lean_nat_dec_le(v___x_3173_, v___x_3174_);
                lean_dec(v___x_3173_);
                if v___x_3175_ == 0 {
                    v_val_3176_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6___redArg(v_buckets_x27_3169_);
                    if v_isShared_3165_ == 0 {
                        lean_ctor_set(v___x_3164_, 1, v_val_3176_);
                        lean_ctor_set(v___x_3164_, 0, v_size_x27_3167_);
                        v___x_3178_ = v___x_3164_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_size_x27_3167_);
                        lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_val_3176_);
                        v___x_3178_ = v_reuseFailAlloc_3179_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3165_ == 0 {
                        lean_ctor_set(v___x_3164_, 1, v_buckets_x27_3169_);
                        lean_ctor_set(v___x_3164_, 0, v_size_x27_3167_);
                        v___x_3181_ = v___x_3164_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_size_x27_3167_);
                        lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_buckets_x27_3169_);
                        v___x_3181_ = v_reuseFailAlloc_3182_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3178_;
            }
            3 => {
                return v___x_3181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(
    mut v_as_x27_3186_: *mut LeanObject,
    mut v_b_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3186_) == 0 {
                    return v_b_3187_;
                } else {
                    v_head_3188_ = lean_ctor_get(v_as_x27_3186_, 0);
                    v_tail_3189_ = lean_ctor_get(v_as_x27_3186_, 1);
                    v___x_3190_ = lean_box(0);
                    lean_inc(v_head_3188_);
                    v_r_3191_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3___redArg(v_b_3187_, v_head_3188_, v___x_3190_);
                    v_as_x27_3186_ = v_tail_3189_;
                    v_b_3187_ = v_r_3191_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg___boxed(
    mut v_as_x27_3193_: *mut LeanObject,
    mut v_b_3194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3195_: *mut LeanObject = core::ptr::null_mut();
    v_res_3195_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_as_x27_3193_, v_b_3194_);
    lean_dec(v_as_x27_3193_);
    return v_res_3195_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2(
    mut v_m_3196_: *mut LeanObject,
    mut v_l_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    v___x_3198_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_l_3197_, v_m_3196_);
    return v___x_3198_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2___boxed(
    mut v_m_3199_: *mut LeanObject,
    mut v_l_3200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3201_: *mut LeanObject = core::ptr::null_mut();
    v_res_3201_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2(v_m_3199_, v_l_3200_);
    lean_dec(v_l_3200_);
    return v_res_3201_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2()
-> *mut LeanObject {
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    v___x_3205_ = lean_box(0);
    v___x_3206_ = lean_unsigned_to_nat(16);
    v___x_3207_ = lean_mk_array(v___x_3206_, v___x_3205_);
    return v___x_3207_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3()
-> *mut LeanObject {
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    v___x_3208_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__2);
    v___x_3209_ = lean_unsigned_to_nat(0);
    v___x_3210_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3210_, 0, v___x_3209_);
    lean_ctor_set(v___x_3210_, 1, v___x_3208_);
    return v___x_3210_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(
    mut v_declName_3211_: *mut LeanObject,
    mut v_a_3212_: *mut LeanObject,
    mut v_a_3213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3222_: u8 = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3231_: u8 = 0;
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: u8 = 0;
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3257_: usize = 0;
    let mut v___x_3258_: usize = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_unused_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3266_: u8 = 0;
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_3211_);
                v___x_3218_ = l_Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0(v_declName_3211_, v_a_3212_, v_a_3213_);
                if lean_obj_tag(v___x_3218_) == 0 {
                    v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
                    v_isSharedCheck_3266_ = (!lean_is_exclusive(v___x_3218_)) as u8;
                    if v_isSharedCheck_3266_ == 0 {
                        v___x_3221_ = v___x_3218_;
                        v_isShared_3222_ = v_isSharedCheck_3266_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3219_);
                        lean_dec(v___x_3218_);
                        v___x_3221_ = lean_box(0);
                        v_isShared_3222_ = v_isSharedCheck_3266_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_3211_);
                    v_a_3267_ = lean_ctor_get(v___x_3218_, 0);
                    v_isSharedCheck_3274_ = (!lean_is_exclusive(v___x_3218_)) as u8;
                    if v_isSharedCheck_3274_ == 0 {
                        v___x_3269_ = v___x_3218_;
                        v_isShared_3270_ = v_isSharedCheck_3274_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3267_);
                        lean_dec(v___x_3218_);
                        v___x_3269_ = lean_box(0);
                        v_isShared_3270_ = v_isSharedCheck_3274_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3216_ = lean_box(0);
                v___x_3217_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3217_, 0, v___x_3216_);
                return v___x_3217_;
            }
            2 => {
                v_type_3228_ = lean_ctor_get(v_a_3219_, 2);
                v_isSharedCheck_3263_ = (!lean_is_exclusive(v_a_3219_)) as u8;
                if v_isSharedCheck_3263_ == 0 {
                    v_unused_3264_ = lean_ctor_get(v_a_3219_, 1);
                    lean_dec(v_unused_3264_);
                    v_unused_3265_ = lean_ctor_get(v_a_3219_, 0);
                    lean_dec(v_unused_3265_);
                    v___x_3230_ = v_a_3219_;
                    v_isShared_3231_ = v_isSharedCheck_3263_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_type_3228_);
                    lean_dec(v_a_3219_);
                    v___x_3230_ = lean_box(0);
                    v_isShared_3231_ = v_isSharedCheck_3263_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_3224_ = lean_box(0);
                if v_isShared_3222_ == 0 {
                    lean_ctor_set(v___x_3221_, 0, v___x_3224_);
                    v___x_3226_ = v___x_3221_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
                    v___x_3226_ = v_reuseFailAlloc_3227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3226_;
            }
            5 => {
                v___x_3232_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__1;
                v___x_3233_ = lean_unsigned_to_nat(3);
                v___x_3234_ = l_Lean_Expr_isAppOfArity(v_type_3228_, v___x_3232_, v___x_3233_);
                if v___x_3234_ == 0 {
                    lean_del_object(v___x_3230_);
                    lean_dec_ref(v_type_3228_);
                    lean_del_object(v___x_3221_);
                    lean_dec(v_declName_3211_);
                    state = 1;
                    continue;
                } else {
                    v___x_3235_ = l_Lean_Expr_appFn_x21(v_type_3228_);
                    v___x_3236_ = l_Lean_Expr_appArg_x21(v___x_3235_);
                    lean_dec_ref(v___x_3235_);
                    if lean_obj_tag(v___x_3236_) == 4 {
                        v_declName_3237_ = lean_ctor_get(v___x_3236_, 0);
                        lean_inc(v_declName_3237_);
                        v_us_3238_ = lean_ctor_get(v___x_3236_, 1);
                        lean_inc(v_us_3238_);
                        lean_dec_ref_known(v___x_3236_, 2);
                        v___x_3239_ = l_Lean_Expr_appArg_x21(v_type_3228_);
                        lean_dec_ref(v_type_3228_);
                        if lean_obj_tag(v___x_3239_) == 4 {
                            v_declName_3240_ = lean_ctor_get(v___x_3239_, 0);
                            lean_inc(v_declName_3240_);
                            v_us_3241_ = lean_ctor_get(v___x_3239_, 1);
                            lean_inc(v_us_3241_);
                            lean_dec_ref_known(v___x_3239_, 2);
                            v___x_3250_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___closed__3);
                            v___x_3251_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_us_3238_, v___x_3250_);
                            v_size_3252_ = lean_ctor_get(v___x_3251_, 0);
                            lean_inc(v_size_3252_);
                            v_buckets_3253_ = lean_ctor_get(v___x_3251_, 1);
                            lean_inc_ref(v_buckets_3253_);
                            lean_dec_ref(v___x_3251_);
                            v___x_3254_ = l_List_lengthTR___redArg(v_us_3238_);
                            v___x_3255_ = lean_nat_dec_eq(v_size_3252_, v___x_3254_);
                            lean_dec(v___x_3254_);
                            lean_dec(v_size_3252_);
                            if v___x_3255_ == 0 {
                                lean_dec_ref(v_buckets_3253_);
                                v___y_3243_ = v___x_3255_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3256_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__3___closed__0;
                                v_sz_3257_ = lean_array_size(v_buckets_3253_);
                                v___x_3258_ = 0usize;
                                v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__4(v_buckets_3253_, v_sz_3257_, v___x_3258_, v___x_3256_);
                                lean_dec_ref(v_buckets_3253_);
                                v_fst_3260_ = lean_ctor_get(v___x_3259_, 0);
                                lean_inc(v_fst_3260_);
                                lean_dec_ref(v___x_3259_);
                                if lean_obj_tag(v_fst_3260_) == 0 {
                                    v___y_3243_ = v___x_3255_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_val_3261_ = lean_ctor_get(v_fst_3260_, 0);
                                    lean_inc(v_val_3261_);
                                    lean_dec_ref_known(v_fst_3260_, 1);
                                    v___x_3262_ = (lean_unbox(v_val_3261_) as u8);
                                    lean_dec(v_val_3261_);
                                    v___y_3243_ = v___x_3262_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3239_);
                            lean_dec(v_us_3238_);
                            lean_dec(v_declName_3237_);
                            lean_del_object(v___x_3230_);
                            lean_del_object(v___x_3221_);
                            lean_dec(v_declName_3211_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3236_);
                        lean_del_object(v___x_3230_);
                        lean_dec_ref(v_type_3228_);
                        lean_del_object(v___x_3221_);
                        lean_dec(v_declName_3211_);
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                if v___y_3243_ == 0 {
                    lean_dec(v_us_3241_);
                    lean_dec(v_declName_3240_);
                    lean_dec(v_us_3238_);
                    lean_dec(v_declName_3237_);
                    lean_del_object(v___x_3230_);
                    lean_dec(v_declName_3211_);
                    state = 3;
                    continue;
                } else {
                    v___x_3244_ = l_List_beq___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__1(v_us_3238_, v_us_3241_);
                    lean_dec(v_us_3241_);
                    lean_dec(v_us_3238_);
                    if v___x_3244_ == 0 {
                        lean_dec(v_declName_3240_);
                        lean_dec(v_declName_3237_);
                        lean_del_object(v___x_3230_);
                        lean_dec(v_declName_3211_);
                        state = 3;
                        continue;
                    } else {
                        lean_del_object(v___x_3221_);
                        if v_isShared_3231_ == 0 {
                            lean_ctor_set(v___x_3230_, 2, v_declName_3211_);
                            lean_ctor_set(v___x_3230_, 1, v_declName_3240_);
                            lean_ctor_set(v___x_3230_, 0, v_declName_3237_);
                            v___x_3246_ = v___x_3230_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_declName_3237_);
                            lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_declName_3240_);
                            lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_declName_3211_);
                            v___x_3246_ = v_reuseFailAlloc_3249_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            7 => {
                v___x_3247_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3247_, 0, v___x_3246_);
                v___x_3248_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3248_, 0, v___x_3247_);
                return v___x_3248_;
            }
            8 => {
                if v_isShared_3270_ == 0 {
                    v___x_3272_ = v___x_3269_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3273_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_a_3267_);
                    v___x_3272_ = v_reuseFailAlloc_3273_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f___boxed(
    mut v_declName_3275_: *mut LeanObject,
    mut v_a_3276_: *mut LeanObject,
    mut v_a_3277_: *mut LeanObject,
    mut v_a_3278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3279_: *mut LeanObject = core::ptr::null_mut();
    v_res_3279_ =
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(
            v_declName_3275_,
            v_a_3276_,
            v_a_3277_,
        );
    lean_dec(v_a_3277_);
    lean_dec_ref(v_a_3276_);
    return v_res_3279_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0(
    mut v_00_u03b1_3280_: *mut LeanObject,
    mut v_constName_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
    mut v___y_3283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    v___x_3285_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___redArg(v_constName_3281_, v___y_3282_, v___y_3283_);
    return v___x_3285_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_3286_: *mut LeanObject,
    mut v_constName_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
    mut v___y_3289_: *mut LeanObject,
    mut v___y_3290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3291_: *mut LeanObject = core::ptr::null_mut();
    v_res_3291_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0(v_00_u03b1_3286_, v_constName_3287_, v___y_3288_, v___y_3289_);
    lean_dec(v___y_3289_);
    lean_dec_ref(v___y_3288_);
    return v_res_3291_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3(
    mut v_00_u03b2_3292_: *mut LeanObject,
    mut v_m_3293_: *mut LeanObject,
    mut v_a_3294_: *mut LeanObject,
    mut v_b_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    v___x_3296_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3___redArg(v_m_3293_, v_a_3294_, v_b_3295_);
    return v___x_3296_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4(
    mut v_as_3297_: *mut LeanObject,
    mut v_as_x27_3298_: *mut LeanObject,
    mut v_b_3299_: *mut LeanObject,
    mut v_a_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___redArg(v_as_x27_3298_, v_b_3299_);
    return v___x_3301_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4___boxed(
    mut v_as_3302_: *mut LeanObject,
    mut v_as_x27_3303_: *mut LeanObject,
    mut v_b_3304_: *mut LeanObject,
    mut v_a_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3306_: *mut LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__4(v_as_3302_, v_as_x27_3303_, v_b_3304_, v_a_3305_);
    lean_dec(v_as_x27_3303_);
    lean_dec(v_as_3302_);
    return v_res_3306_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3307_: *mut LeanObject,
    mut v_ref_3308_: *mut LeanObject,
    mut v_constName_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    v___x_3313_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___redArg(v_ref_3308_, v_constName_3309_, v___y_3310_, v___y_3311_);
    return v___x_3313_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3314_: *mut LeanObject,
    mut v_ref_3315_: *mut LeanObject,
    mut v_constName_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3320_: *mut LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1(v_00_u03b1_3314_, v_ref_3315_, v_constName_3316_, v___y_3317_, v___y_3318_);
    lean_dec(v___y_3318_);
    lean_dec_ref(v___y_3317_);
    lean_dec(v_ref_3315_);
    return v_res_3320_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5(
    mut v_00_u03b2_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
    mut v_x_3323_: *mut LeanObject,
) -> u8 {
    let mut v___x_3324_: u8 = 0;
    v___x_3324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___redArg(v_a_3322_, v_x_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b2_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
    mut v_x_3327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3328_: u8 = 0;
    let mut v_r_3329_: *mut LeanObject = core::ptr::null_mut();
    v_res_3328_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__5(v_00_u03b2_3325_, v_a_3326_, v_x_3327_);
    lean_dec(v_x_3327_);
    lean_dec(v_a_3326_);
    v_r_3329_ = lean_box((v_res_3328_) as usize);
    return v_r_3329_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6(
    mut v_00_u03b2_3330_: *mut LeanObject,
    mut v_data_3331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    v___x_3332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6___redArg(v_data_3331_);
    return v___x_3332_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03b1_3333_: *mut LeanObject,
    mut v_ref_3334_: *mut LeanObject,
    mut v_msg_3335_: *mut LeanObject,
    mut v_declHint_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    v___x_3340_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_3334_, v_msg_3335_, v_declHint_3336_, v___y_3337_, v___y_3338_);
    return v___x_3340_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03b1_3341_: *mut LeanObject,
    mut v_ref_3342_: *mut LeanObject,
    mut v_msg_3343_: *mut LeanObject,
    mut v_declHint_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3348_: *mut LeanObject = core::ptr::null_mut();
    v_res_3348_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_3341_, v_ref_3342_, v_msg_3343_, v_declHint_3344_, v___y_3345_, v___y_3346_);
    lean_dec(v___y_3346_);
    lean_dec_ref(v___y_3345_);
    lean_dec(v_ref_3342_);
    return v_res_3348_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10(
    mut v_00_u03b2_3349_: *mut LeanObject,
    mut v_i_3350_: *mut LeanObject,
    mut v_source_3351_: *mut LeanObject,
    mut v_target_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    v___x_3353_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10___redArg(v_i_3350_, v_source_3351_, v_target_3352_);
    return v___x_3353_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12(
    mut v_msg_3354_: *mut LeanObject,
    mut v_declHint_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    v___x_3359_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___redArg(v_msg_3354_, v_declHint_3355_, v___y_3357_);
    return v___x_3359_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12___boxed(
    mut v_msg_3360_: *mut LeanObject,
    mut v_declHint_3361_: *mut LeanObject,
    mut v___y_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3365_: *mut LeanObject = core::ptr::null_mut();
    v_res_3365_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__9_spec__12(v_msg_3360_, v_declHint_3361_, v___y_3362_, v___y_3363_);
    lean_dec(v___y_3363_);
    lean_dec_ref(v___y_3362_);
    return v_res_3365_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10(
    mut v_00_u03b1_3366_: *mut LeanObject,
    mut v_ref_3367_: *mut LeanObject,
    mut v_msg_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    v___x_3372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___redArg(v_ref_3367_, v_msg_3368_, v___y_3369_, v___y_3370_);
    return v___x_3372_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10___boxed(
    mut v_00_u03b1_3373_: *mut LeanObject,
    mut v_ref_3374_: *mut LeanObject,
    mut v_msg_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
    mut v___y_3377_: *mut LeanObject,
    mut v___y_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3379_: *mut LeanObject = core::ptr::null_mut();
    v_res_3379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10(v_00_u03b1_3373_, v_ref_3374_, v_msg_3375_, v___y_3376_, v___y_3377_);
    lean_dec(v___y_3377_);
    lean_dec_ref(v___y_3376_);
    lean_dec(v_ref_3374_);
    return v_res_3379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14(
    mut v_00_u03b2_3380_: *mut LeanObject,
    mut v_x_3381_: *mut LeanObject,
    mut v_x_3382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    v___x_3383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__2_spec__3_spec__6_spec__10_spec__14___redArg(v_x_3381_, v_x_3382_);
    return v___x_3383_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14(
    mut v_00_u03b1_3384_: *mut LeanObject,
    mut v_msg_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    v___x_3389_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v_msg_3385_, v___y_3386_, v___y_3387_);
    return v___x_3389_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___boxed(
    mut v_00_u03b1_3390_: *mut LeanObject,
    mut v_msg_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3395_: *mut LeanObject = core::ptr::null_mut();
    v_res_3395_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14(v_00_u03b1_3390_, v_msg_3391_, v___y_3392_, v___y_3393_);
    lean_dec(v___y_3393_);
    lean_dec_ref(v___y_3392_);
    return v_res_3395_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    v___x_3396_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3396_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    v___x_3397_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__0);
    v___x_3398_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3398_, 0, v___x_3397_);
    return v___x_3398_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__1);
    v___x_3400_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3400_, 0, v___x_3399_);
    lean_ctor_set(v___x_3400_, 1, v___x_3399_);
    return v___x_3400_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(
    mut v_ext_3401_: *mut LeanObject,
    mut v_b_3402_: *mut LeanObject,
    mut v_kind_3403_: u8,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut v_unused_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_3407_ = lean_ctor_get(v___y_3404_, 6);
                v___x_3408_ = lean_st_ref_take(v___y_3405_);
                v_env_3409_ = lean_ctor_get(v___x_3408_, 0);
                v_nextMacroScope_3410_ = lean_ctor_get(v___x_3408_, 1);
                v_ngen_3411_ = lean_ctor_get(v___x_3408_, 2);
                v_auxDeclNGen_3412_ = lean_ctor_get(v___x_3408_, 3);
                v_traceState_3413_ = lean_ctor_get(v___x_3408_, 4);
                v_messages_3414_ = lean_ctor_get(v___x_3408_, 6);
                v_infoState_3415_ = lean_ctor_get(v___x_3408_, 7);
                v_snapshotTasks_3416_ = lean_ctor_get(v___x_3408_, 8);
                v_isSharedCheck_3428_ = (!lean_is_exclusive(v___x_3408_)) as u8;
                if v_isSharedCheck_3428_ == 0 {
                    v_unused_3429_ = lean_ctor_get(v___x_3408_, 5);
                    lean_dec(v_unused_3429_);
                    v___x_3418_ = v___x_3408_;
                    v_isShared_3419_ = v_isSharedCheck_3428_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3416_);
                    lean_inc(v_infoState_3415_);
                    lean_inc(v_messages_3414_);
                    lean_inc(v_traceState_3413_);
                    lean_inc(v_auxDeclNGen_3412_);
                    lean_inc(v_ngen_3411_);
                    lean_inc(v_nextMacroScope_3410_);
                    lean_inc(v_env_3409_);
                    lean_dec(v___x_3408_);
                    v___x_3418_ = lean_box(0);
                    v_isShared_3419_ = v_isSharedCheck_3428_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_3407_);
                v___x_3420_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_3409_,
                    v_ext_3401_,
                    v_b_3402_,
                    v_kind_3403_,
                    v_currNamespace_3407_,
                );
                v___x_3421_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2);
                if v_isShared_3419_ == 0 {
                    lean_ctor_set(v___x_3418_, 5, v___x_3421_);
                    lean_ctor_set(v___x_3418_, 0, v___x_3420_);
                    v___x_3423_ = v___x_3418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3420_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_nextMacroScope_3410_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 2, v_ngen_3411_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 3, v_auxDeclNGen_3412_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 4, v_traceState_3413_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 5, v___x_3421_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 6, v_messages_3414_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 7, v_infoState_3415_);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 8, v_snapshotTasks_3416_);
                    v___x_3423_ = v_reuseFailAlloc_3427_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3424_ = lean_st_ref_set(v___y_3405_, v___x_3423_);
                v___x_3425_ = lean_box(0);
                v___x_3426_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3426_, 0, v___x_3425_);
                return v___x_3426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___boxed(
    mut v_ext_3430_: *mut LeanObject,
    mut v_b_3431_: *mut LeanObject,
    mut v_kind_3432_: *mut LeanObject,
    mut v___y_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3436_: u8 = 0;
    let mut v_res_3437_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3436_ = (lean_unbox(v_kind_3432_) as u8);
    v_res_3437_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(
        v_ext_3430_,
        v_b_3431_,
        v_kind_boxed_3436_,
        v___y_3433_,
        v___y_3434_,
    );
    lean_dec(v___y_3434_);
    lean_dec_ref(v___y_3433_);
    return v_res_3437_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0(
    mut v_00_u03b1_3438_: *mut LeanObject,
    mut v_00_u03b2_3439_: *mut LeanObject,
    mut v_00_u03c3_3440_: *mut LeanObject,
    mut v_ext_3441_: *mut LeanObject,
    mut v_b_3442_: *mut LeanObject,
    mut v_kind_3443_: u8,
    mut v___y_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    v___x_3447_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(
        v_ext_3441_,
        v_b_3442_,
        v_kind_3443_,
        v___y_3444_,
        v___y_3445_,
    );
    return v___x_3447_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___boxed(
    mut v_00_u03b1_3448_: *mut LeanObject,
    mut v_00_u03b2_3449_: *mut LeanObject,
    mut v_00_u03c3_3450_: *mut LeanObject,
    mut v_ext_3451_: *mut LeanObject,
    mut v_b_3452_: *mut LeanObject,
    mut v_kind_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
    mut v___y_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3457_: u8 = 0;
    let mut v_res_3458_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3457_ = (lean_unbox(v_kind_3453_) as u8);
    v_res_3458_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0(
        v_00_u03b1_3448_,
        v_00_u03b2_3449_,
        v_00_u03c3_3450_,
        v_ext_3451_,
        v_b_3452_,
        v_kind_boxed_3457_,
        v___y_3454_,
        v___y_3455_,
    );
    lean_dec(v___y_3455_);
    lean_dec_ref(v___y_3454_);
    return v_res_3458_;
}
pub unsafe fn _init_l_Lean_Compiler_CSimp_add___closed__1() -> *mut LeanObject {
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    v___x_3460_ = l_Lean_Compiler_CSimp_add___closed__0;
    v___x_3461_ = l_Lean_stringToMessageData(v___x_3460_);
    return v___x_3461_;
}
pub unsafe fn l_Lean_Compiler_CSimp_add(
    mut v_declName_3462_: *mut LeanObject,
    mut v_kind_3463_: u8,
    mut v_a_3464_: *mut LeanObject,
    mut v_a_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3467_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f(v_declName_3462_, v_a_3464_, v_a_3465_);
                if lean_obj_tag(v___x_3467_) == 0 {
                    v_a_3468_ = lean_ctor_get(v___x_3467_, 0);
                    lean_inc(v_a_3468_);
                    lean_dec_ref_known(v___x_3467_, 1);
                    if lean_obj_tag(v_a_3468_) == 1 {
                        v_val_3469_ = lean_ctor_get(v_a_3468_, 0);
                        lean_inc(v_val_3469_);
                        lean_dec_ref_known(v_a_3468_, 1);
                        v___x_3470_ = l_Lean_Compiler_CSimp_ext;
                        v___x_3471_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg(v___x_3470_, v_val_3469_, v_kind_3463_, v_a_3464_, v_a_3465_);
                        return v___x_3471_;
                    } else {
                        lean_dec(v_a_3468_);
                        v___x_3472_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_add___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Compiler_CSimp_add___closed__1_once),
                            _init_l_Lean_Compiler_CSimp_add___closed__1,
                        );
                        v___x_3473_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v___x_3472_, v_a_3464_, v_a_3465_);
                        return v___x_3473_;
                    }
                } else {
                    v_a_3474_ = lean_ctor_get(v___x_3467_, 0);
                    v_isSharedCheck_3481_ = (!lean_is_exclusive(v___x_3467_)) as u8;
                    if v_isSharedCheck_3481_ == 0 {
                        v___x_3476_ = v___x_3467_;
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3474_);
                        lean_dec(v___x_3467_);
                        v___x_3476_ = lean_box(0);
                        v_isShared_3477_ = v_isSharedCheck_3481_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3477_ == 0 {
                    v___x_3479_ = v___x_3476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
                    v___x_3479_ = v_reuseFailAlloc_3480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_CSimp_add___boxed(
    mut v_declName_3482_: *mut LeanObject,
    mut v_kind_3483_: *mut LeanObject,
    mut v_a_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
    mut v_a_3486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3487_: u8 = 0;
    let mut v_res_3488_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3487_ = (lean_unbox(v_kind_3483_) as u8);
    v_res_3488_ =
        l_Lean_Compiler_CSimp_add(v_declName_3482_, v_kind_boxed_3487_, v_a_3484_, v_a_3485_);
    lean_dec(v_a_3485_);
    lean_dec_ref(v_a_3484_);
    return v_res_3488_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0(
    mut v___x_3489_: *mut LeanObject,
    mut v_declName_3490_: *mut LeanObject,
    mut v_stx_3491_: *mut LeanObject,
    mut v_attrKind_3492_: u8,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3501_: u8 = 0;
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3506_: u8 = 0;
    let mut v_unused_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3496_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3491_, v___y_3493_, v___y_3494_);
                if lean_obj_tag(v___x_3496_) == 0 {
                    lean_dec_ref_known(v___x_3496_, 1);
                    lean_inc(v_declName_3490_);
                    v___x_3497_ = l_Lean_ensureAttrDeclIsPublic(
                        v___x_3489_,
                        v_declName_3490_,
                        v_attrKind_3492_,
                        v___y_3493_,
                        v___y_3494_,
                    );
                    if lean_obj_tag(v___x_3497_) == 0 {
                        lean_dec_ref_known(v___x_3497_, 1);
                        v___x_3498_ = l_Lean_Compiler_CSimp_add(
                            v_declName_3490_,
                            v_attrKind_3492_,
                            v___y_3493_,
                            v___y_3494_,
                        );
                        if lean_obj_tag(v___x_3498_) == 0 {
                            v_isSharedCheck_3506_ = (!lean_is_exclusive(v___x_3498_)) as u8;
                            if v_isSharedCheck_3506_ == 0 {
                                v_unused_3507_ = lean_ctor_get(v___x_3498_, 0);
                                lean_dec(v_unused_3507_);
                                v___x_3500_ = v___x_3498_;
                                v_isShared_3501_ = v_isSharedCheck_3506_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_3498_);
                                v___x_3500_ = lean_box(0);
                                v_isShared_3501_ = v_isSharedCheck_3506_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3498_;
                        }
                    } else {
                        lean_dec(v_declName_3490_);
                        return v___x_3497_;
                    }
                } else {
                    lean_dec(v_declName_3490_);
                    lean_dec(v___x_3489_);
                    return v___x_3496_;
                }
            }
            1 => {
                v___x_3502_ = lean_box(0);
                if v_isShared_3501_ == 0 {
                    lean_ctor_set(v___x_3500_, 0, v___x_3502_);
                    v___x_3504_ = v___x_3500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
                    v___x_3504_ = v_reuseFailAlloc_3505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0___boxed(
    mut v___x_3508_: *mut LeanObject,
    mut v_declName_3509_: *mut LeanObject,
    mut v_stx_3510_: *mut LeanObject,
    mut v_attrKind_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_attrKind_boxed_3515_: u8 = 0;
    let mut v_res_3516_: *mut LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_3515_ = (lean_unbox(v_attrKind_3511_) as u8);
    v_res_3516_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__0(
        v___x_3508_,
        v_declName_3509_,
        v_stx_3510_,
        v_attrKind_boxed_3515_,
        v___y_3512_,
        v___y_3513_,
    );
    lean_dec(v___y_3513_);
    lean_dec_ref(v___y_3512_);
    return v_res_3516_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    v___x_3518_ =
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__0;
    v___x_3519_ = l_Lean_stringToMessageData(v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    v___x_3521_ =
        l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__2;
    v___x_3522_ = l_Lean_stringToMessageData(v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1(
    mut v___x_3523_: *mut LeanObject,
    mut v_decl_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
    mut v___y_3526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    v___x_3528_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__1);
    v___x_3529_ = l_Lean_MessageData_ofName(v___x_3523_);
    v___x_3530_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3530_, 0, v___x_3528_);
    lean_ctor_set(v___x_3530_, 1, v___x_3529_);
    v___x_3531_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3_once), _init_l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___closed__3);
    v___x_3532_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3532_, 0, v___x_3530_);
    lean_ctor_set(v___x_3532_, 1, v___x_3531_);
    v___x_3533_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14___redArg(v___x_3532_, v___y_3525_, v___y_3526_);
    return v___x_3533_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1___boxed(
    mut v___x_3534_: *mut LeanObject,
    mut v_decl_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
    mut v___y_3538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3539_: *mut LeanObject = core::ptr::null_mut();
    v_res_3539_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___lam__1(
        v___x_3534_,
        v_decl_3535_,
        v___y_3536_,
        v___y_3537_,
    );
    lean_dec(v___y_3537_);
    lean_dec_ref(v___y_3536_);
    lean_dec(v_decl_3535_);
    return v_res_3539_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn() -> *mut LeanObject
{
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    v___x_3588_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__18;
    v___x_3589_ = l_Lean_registerBuiltinAttribute(v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___boxed(
    mut v_a_3590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3591_: *mut LeanObject = core::ptr::null_mut();
    v_res_3591_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn();
    return v_res_3591_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1()
-> *mut LeanObject {
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3594_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___closed__11;
    v___x_3595_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___closed__0;
    v___x_3596_ = l_Lean_addBuiltinDocString(v___x_3594_, v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1___boxed(
    mut v_a_3597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3598_: *mut LeanObject = core::ptr::null_mut();
    v_res_3598_ = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1();
    return v_res_3598_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(
    mut v___y_3599_: *mut LeanObject,
    mut v_isExporting_3600_: u8,
    mut v___x_3601_: *mut LeanObject,
    mut v_a_x3f_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3623_: u8 = 0;
    let mut v_unused_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3604_ = lean_st_ref_take(v___y_3599_);
                v_env_3605_ = lean_ctor_get(v___x_3604_, 0);
                v_nextMacroScope_3606_ = lean_ctor_get(v___x_3604_, 1);
                v_ngen_3607_ = lean_ctor_get(v___x_3604_, 2);
                v_auxDeclNGen_3608_ = lean_ctor_get(v___x_3604_, 3);
                v_traceState_3609_ = lean_ctor_get(v___x_3604_, 4);
                v_messages_3610_ = lean_ctor_get(v___x_3604_, 6);
                v_infoState_3611_ = lean_ctor_get(v___x_3604_, 7);
                v_snapshotTasks_3612_ = lean_ctor_get(v___x_3604_, 8);
                v_isSharedCheck_3623_ = (!lean_is_exclusive(v___x_3604_)) as u8;
                if v_isSharedCheck_3623_ == 0 {
                    v_unused_3624_ = lean_ctor_get(v___x_3604_, 5);
                    lean_dec(v_unused_3624_);
                    v___x_3614_ = v___x_3604_;
                    v_isShared_3615_ = v_isSharedCheck_3623_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3612_);
                    lean_inc(v_infoState_3611_);
                    lean_inc(v_messages_3610_);
                    lean_inc(v_traceState_3609_);
                    lean_inc(v_auxDeclNGen_3608_);
                    lean_inc(v_ngen_3607_);
                    lean_inc(v_nextMacroScope_3606_);
                    lean_inc(v_env_3605_);
                    lean_dec(v___x_3604_);
                    v___x_3614_ = lean_box(0);
                    v_isShared_3615_ = v_isSharedCheck_3623_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3616_ = l_Lean_Environment_setExporting(v_env_3605_, v_isExporting_3600_);
                if v_isShared_3615_ == 0 {
                    lean_ctor_set(v___x_3614_, 5, v___x_3601_);
                    lean_ctor_set(v___x_3614_, 0, v___x_3616_);
                    v___x_3618_ = v___x_3614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3616_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_nextMacroScope_3606_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 2, v_ngen_3607_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 3, v_auxDeclNGen_3608_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 4, v_traceState_3609_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 5, v___x_3601_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 6, v_messages_3610_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 7, v_infoState_3611_);
                    lean_ctor_set(v_reuseFailAlloc_3622_, 8, v_snapshotTasks_3612_);
                    v___x_3618_ = v_reuseFailAlloc_3622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3619_ = lean_st_ref_set(v___y_3599_, v___x_3618_);
                v___x_3620_ = lean_box(0);
                v___x_3621_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3621_, 0, v___x_3620_);
                return v___x_3621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0___boxed(
    mut v___y_3625_: *mut LeanObject,
    mut v_isExporting_3626_: *mut LeanObject,
    mut v___x_3627_: *mut LeanObject,
    mut v_a_x3f_3628_: *mut LeanObject,
    mut v___y_3629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_3630_: u8 = 0;
    let mut v_res_3631_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3630_ = (lean_unbox(v_isExporting_3626_) as u8);
    v_res_3631_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(v___y_3625_, v_isExporting_boxed_3630_, v___x_3627_, v_a_x3f_3628_);
    lean_dec(v_a_x3f_3628_);
    lean_dec(v___y_3625_);
    return v_res_3631_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(
    mut v_x_3632_: *mut LeanObject,
    mut v_isExporting_3633_: u8,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3639_: u8 = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3651_: u8 = 0;
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3667_: u8 = 0;
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut v_unused_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_a_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3680_: u8 = 0;
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3684_: u8 = 0;
    let mut v_unused_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut v_unused_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3637_ = lean_st_ref_get(v___y_3635_);
                v_env_3638_ = lean_ctor_get(v___x_3637_, 0);
                lean_inc_ref(v_env_3638_);
                lean_dec(v___x_3637_);
                v_isExporting_3639_ = lean_ctor_get_uint8(
                    v_env_3638_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_3638_);
                v___x_3640_ = lean_st_ref_take(v___y_3635_);
                v_env_3641_ = lean_ctor_get(v___x_3640_, 0);
                v_nextMacroScope_3642_ = lean_ctor_get(v___x_3640_, 1);
                v_ngen_3643_ = lean_ctor_get(v___x_3640_, 2);
                v_auxDeclNGen_3644_ = lean_ctor_get(v___x_3640_, 3);
                v_traceState_3645_ = lean_ctor_get(v___x_3640_, 4);
                v_messages_3646_ = lean_ctor_get(v___x_3640_, 6);
                v_infoState_3647_ = lean_ctor_get(v___x_3640_, 7);
                v_snapshotTasks_3648_ = lean_ctor_get(v___x_3640_, 8);
                v_isSharedCheck_3687_ = (!lean_is_exclusive(v___x_3640_)) as u8;
                if v_isSharedCheck_3687_ == 0 {
                    v_unused_3688_ = lean_ctor_get(v___x_3640_, 5);
                    lean_dec(v_unused_3688_);
                    v___x_3650_ = v___x_3640_;
                    v_isShared_3651_ = v_isSharedCheck_3687_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3648_);
                    lean_inc(v_infoState_3647_);
                    lean_inc(v_messages_3646_);
                    lean_inc(v_traceState_3645_);
                    lean_inc(v_auxDeclNGen_3644_);
                    lean_inc(v_ngen_3643_);
                    lean_inc(v_nextMacroScope_3642_);
                    lean_inc(v_env_3641_);
                    lean_dec(v___x_3640_);
                    v___x_3650_ = lean_box(0);
                    v_isShared_3651_ = v_isSharedCheck_3687_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3652_ = l_Lean_Environment_setExporting(v_env_3641_, v_isExporting_3633_);
                v___x_3653_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2);
                if v_isShared_3651_ == 0 {
                    lean_ctor_set(v___x_3650_, 5, v___x_3653_);
                    lean_ctor_set(v___x_3650_, 0, v___x_3652_);
                    v___x_3655_ = v___x_3650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3652_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_nextMacroScope_3642_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_ngen_3643_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 3, v_auxDeclNGen_3644_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 4, v_traceState_3645_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 5, v___x_3653_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 6, v_messages_3646_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 7, v_infoState_3647_);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 8, v_snapshotTasks_3648_);
                    v___x_3655_ = v_reuseFailAlloc_3686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3656_ = lean_st_ref_set(v___y_3635_, v___x_3655_);
                lean_inc(v___y_3635_);
                lean_inc_ref(v___y_3634_);
                v_r_3657_ = lean_apply_3(v_x_3632_, v___y_3634_, v___y_3635_, lean_box(0));
                if lean_obj_tag(v_r_3657_) == 0 {
                    v_a_3658_ = lean_ctor_get(v_r_3657_, 0);
                    v_isSharedCheck_3674_ = (!lean_is_exclusive(v_r_3657_)) as u8;
                    if v_isSharedCheck_3674_ == 0 {
                        v___x_3660_ = v_r_3657_;
                        v_isShared_3661_ = v_isSharedCheck_3674_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3658_);
                        lean_dec(v_r_3657_);
                        v___x_3660_ = lean_box(0);
                        v_isShared_3661_ = v_isSharedCheck_3674_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3675_ = lean_ctor_get(v_r_3657_, 0);
                    lean_inc(v_a_3675_);
                    lean_dec_ref_known(v_r_3657_, 1);
                    v___x_3676_ = lean_box(0);
                    v___x_3677_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(v___y_3635_, v_isExporting_3639_, v___x_3653_, v___x_3676_);
                    v_isSharedCheck_3684_ = (!lean_is_exclusive(v___x_3677_)) as u8;
                    if v_isSharedCheck_3684_ == 0 {
                        v_unused_3685_ = lean_ctor_get(v___x_3677_, 0);
                        lean_dec(v_unused_3685_);
                        v___x_3679_ = v___x_3677_;
                        v_isShared_3680_ = v_isSharedCheck_3684_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_3677_);
                        v___x_3679_ = lean_box(0);
                        v_isShared_3680_ = v_isSharedCheck_3684_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_3658_);
                if v_isShared_3661_ == 0 {
                    lean_ctor_set_tag(v___x_3660_, 1);
                    v___x_3663_ = v___x_3660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3658_);
                    v___x_3663_ = v_reuseFailAlloc_3673_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3664_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___lam__0(v___y_3635_, v_isExporting_3639_, v___x_3653_, v___x_3663_);
                lean_dec_ref(v___x_3663_);
                v_isSharedCheck_3671_ = (!lean_is_exclusive(v___x_3664_)) as u8;
                if v_isSharedCheck_3671_ == 0 {
                    v_unused_3672_ = lean_ctor_get(v___x_3664_, 0);
                    lean_dec(v_unused_3672_);
                    v___x_3666_ = v___x_3664_;
                    v_isShared_3667_ = v_isSharedCheck_3671_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_3664_);
                    v___x_3666_ = lean_box(0);
                    v_isShared_3667_ = v_isSharedCheck_3671_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3667_ == 0 {
                    lean_ctor_set(v___x_3666_, 0, v_a_3658_);
                    v___x_3669_ = v___x_3666_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3658_);
                    v___x_3669_ = v_reuseFailAlloc_3670_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3669_;
            }
            7 => {
                if v_isShared_3680_ == 0 {
                    lean_ctor_set_tag(v___x_3679_, 1);
                    lean_ctor_set(v___x_3679_, 0, v_a_3675_);
                    v___x_3682_ = v___x_3679_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3675_);
                    v___x_3682_ = v_reuseFailAlloc_3683_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg___boxed(
    mut v_x_3689_: *mut LeanObject,
    mut v_isExporting_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_3694_: u8 = 0;
    let mut v_res_3695_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3694_ = (lean_unbox(v_isExporting_3690_) as u8);
    v_res_3695_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(v_x_3689_, v_isExporting_boxed_3694_, v___y_3691_, v___y_3692_);
    lean_dec(v___y_3692_);
    lean_dec_ref(v___y_3691_);
    return v_res_3695_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(
    mut v_x_3696_: *mut LeanObject,
    mut v_when_3697_: u8,
    mut v___y_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_3697_ == 0 {
        let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_3699_);
        lean_inc_ref(v___y_3698_);
        v___x_3701_ = lean_apply_3(v_x_3696_, v___y_3698_, v___y_3699_, lean_box(0));
        return v___x_3701_;
    } else {
        let mut v___x_3702_: u8 = 0;
        let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
        v___x_3702_ = 0;
        v___x_3703_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(v_x_3696_, v___x_3702_, v___y_3698_, v___y_3699_);
        return v___x_3703_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg___boxed(
    mut v_x_3704_: *mut LeanObject,
    mut v_when_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_3709_: u8 = 0;
    let mut v_res_3710_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_3709_ = (lean_unbox(v_when_3705_) as u8);
    v_res_3710_ =
        l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(
            v_x_3704_,
            v_when_boxed_3709_,
            v___y_3706_,
            v___y_3707_,
        );
    lean_dec(v___y_3707_);
    lean_dec_ref(v___y_3706_);
    return v_res_3710_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(
    mut v_a_3711_: *mut LeanObject,
    mut v_x_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3712_) == 0 {
                    v___x_3713_ = lean_box(0);
                    return v___x_3713_;
                } else {
                    v_key_3714_ = lean_ctor_get(v_x_3712_, 0);
                    v_value_3715_ = lean_ctor_get(v_x_3712_, 1);
                    v_tail_3716_ = lean_ctor_get(v_x_3712_, 2);
                    v___x_3717_ = lean_name_eq(v_key_3714_, v_a_3711_);
                    if v___x_3717_ == 0 {
                        v_x_3712_ = v_tail_3716_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3715_);
                        v___x_3719_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3719_, 0, v_value_3715_);
                        return v___x_3719_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_3720_: *mut LeanObject,
    mut v_x_3721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3722_: *mut LeanObject = core::ptr::null_mut();
    v_res_3722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(v_a_3720_, v_x_3721_);
    lean_dec(v_x_3721_);
    lean_dec(v_a_3720_);
    return v_res_3722_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(
    mut v_m_3723_: *mut LeanObject,
    mut v_a_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3728_: u64 = 0;
    let mut v___x_3729_: u64 = 0;
    let mut v___x_3730_: u64 = 0;
    let mut v_fold_3731_: u64 = 0;
    let mut v___x_3732_: u64 = 0;
    let mut v___x_3733_: u64 = 0;
    let mut v___x_3734_: u64 = 0;
    let mut v___x_3735_: usize = 0;
    let mut v___x_3736_: usize = 0;
    let mut v___x_3737_: usize = 0;
    let mut v___x_3738_: usize = 0;
    let mut v___x_3739_: usize = 0;
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: u64 = 0;
    let mut v_hash_3743_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3725_ = lean_ctor_get(v_m_3723_, 1);
                v___x_3726_ = lean_array_get_size(v_buckets_3725_);
                if lean_obj_tag(v_a_3724_) == 0 {
                    v___x_3742_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_3728_ = v___x_3742_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3743_ = lean_ctor_get_uint64(
                        v_a_3724_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3728_ = v_hash_3743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3729_ = 32u64;
                v___x_3730_ = lean_uint64_shift_right(v___y_3728_, v___x_3729_);
                v_fold_3731_ = lean_uint64_xor(v___y_3728_, v___x_3730_);
                v___x_3732_ = 16u64;
                v___x_3733_ = lean_uint64_shift_right(v_fold_3731_, v___x_3732_);
                v___x_3734_ = lean_uint64_xor(v_fold_3731_, v___x_3733_);
                v___x_3735_ = lean_uint64_to_usize(v___x_3734_);
                v___x_3736_ = lean_usize_of_nat(v___x_3726_);
                v___x_3737_ = 1usize;
                v___x_3738_ = lean_usize_sub(v___x_3736_, v___x_3737_);
                v___x_3739_ = lean_usize_land(v___x_3735_, v___x_3738_);
                v___x_3740_ = lean_array_uget_borrowed(v_buckets_3725_, v___x_3739_);
                v___x_3741_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(v_a_3724_, v___x_3740_);
                return v___x_3741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg___boxed(
    mut v_m_3744_: *mut LeanObject,
    mut v_a_3745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3746_: *mut LeanObject = core::ptr::null_mut();
    v_res_3746_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_m_3744_, v_a_3745_);
    lean_dec(v_a_3745_);
    lean_dec_ref(v_m_3744_);
    return v_res_3746_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(
    mut v_keys_3747_: *mut LeanObject,
    mut v_i_3748_: *mut LeanObject,
    mut v_k_3749_: *mut LeanObject,
) -> u8 {
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: u8 = 0;
    let mut v_k_x27_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3750_ = lean_array_get_size(v_keys_3747_);
                v___x_3751_ = lean_nat_dec_lt(v_i_3748_, v___x_3750_);
                if v___x_3751_ == 0 {
                    lean_dec(v_i_3748_);
                    return v___x_3751_;
                } else {
                    v_k_x27_3752_ = lean_array_fget_borrowed(v_keys_3747_, v_i_3748_);
                    v___x_3753_ = l_Lean_instBEqExtraModUse_beq(v_k_3749_, v_k_x27_3752_);
                    if v___x_3753_ == 0 {
                        v___x_3754_ = lean_unsigned_to_nat(1);
                        v___x_3755_ = lean_nat_add(v_i_3748_, v___x_3754_);
                        lean_dec(v_i_3748_);
                        v_i_3748_ = v___x_3755_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_3748_);
                        return v___x_3753_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg___boxed(
    mut v_keys_3757_: *mut LeanObject,
    mut v_i_3758_: *mut LeanObject,
    mut v_k_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3760_: u8 = 0;
    let mut v_r_3761_: *mut LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(v_keys_3757_, v_i_3758_, v_k_3759_);
    lean_dec_ref(v_k_3759_);
    lean_dec_ref(v_keys_3757_);
    v_r_3761_ = lean_box((v_res_3760_) as usize);
    return v_r_3761_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(
    mut v_x_3762_: *mut LeanObject,
    mut v_x_3763_: usize,
    mut v_x_3764_: *mut LeanObject,
) -> u8 {
    let mut v_es_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: usize = 0;
    let mut v___x_3768_: usize = 0;
    let mut v___x_3769_: usize = 0;
    let mut v_j_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: u8 = 0;
    let mut v_node_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: usize = 0;
    let mut v___x_3777_: u8 = 0;
    let mut v_ks_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3762_) == 0 {
                    v_es_3765_ = lean_ctor_get(v_x_3762_, 0);
                    v___x_3766_ = lean_box(2);
                    v___x_3767_ = 5usize;
                    v___x_3768_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3769_ = lean_usize_land(v_x_3763_, v___x_3768_);
                    v_j_3770_ = lean_usize_to_nat(v___x_3769_);
                    v___x_3771_ = lean_array_get_borrowed(v___x_3766_, v_es_3765_, v_j_3770_);
                    lean_dec(v_j_3770_);
                    match lean_obj_tag(v___x_3771_) {
                        0 => {
                            v_key_3772_ = lean_ctor_get(v___x_3771_, 0);
                            v___x_3773_ = l_Lean_instBEqExtraModUse_beq(v_x_3764_, v_key_3772_);
                            return v___x_3773_;
                        }
                        1 => {
                            v_node_3774_ = lean_ctor_get(v___x_3771_, 0);
                            v___x_3775_ = lean_usize_shift_right(v_x_3763_, v___x_3767_);
                            v_x_3762_ = v_node_3774_;
                            v_x_3763_ = v___x_3775_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3777_ = 0;
                            return v___x_3777_;
                        }
                    }
                } else {
                    v_ks_3778_ = lean_ctor_get(v_x_3762_, 0);
                    v___x_3779_ = lean_unsigned_to_nat(0);
                    v___x_3780_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(v_ks_3778_, v___x_3779_, v_x_3764_);
                    return v___x_3780_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg___boxed(
    mut v_x_3781_: *mut LeanObject,
    mut v_x_3782_: *mut LeanObject,
    mut v_x_3783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5089__boxed_3784_: usize = 0;
    let mut v_res_3785_: u8 = 0;
    let mut v_r_3786_: *mut LeanObject = core::ptr::null_mut();
    v_x_5089__boxed_3784_ = lean_unbox_usize(v_x_3782_);
    lean_dec(v_x_3782_);
    v_res_3785_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(v_x_3781_, v_x_5089__boxed_3784_, v_x_3783_);
    lean_dec_ref(v_x_3783_);
    lean_dec_ref(v_x_3781_);
    v_r_3786_ = lean_box((v_res_3785_) as usize);
    return v_r_3786_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(
    mut v_x_3787_: *mut LeanObject,
    mut v_x_3788_: *mut LeanObject,
) -> u8 {
    let mut v___x_3789_: u64 = 0;
    let mut v___x_3790_: usize = 0;
    let mut v___x_3791_: u8 = 0;
    v___x_3789_ = l_Lean_instHashableExtraModUse_hash(v_x_3788_);
    v___x_3790_ = lean_uint64_to_usize(v___x_3789_);
    v___x_3791_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(v_x_3787_, v___x_3790_, v_x_3788_);
    return v___x_3791_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_3792_: *mut LeanObject,
    mut v_x_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3794_: u8 = 0;
    let mut v_r_3795_: *mut LeanObject = core::ptr::null_mut();
    v_res_3794_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(v_x_3792_, v_x_3793_);
    lean_dec_ref(v_x_3793_);
    lean_dec_ref(v_x_3792_);
    v_r_3795_ = lean_box((v_res_3794_) as usize);
    return v_r_3795_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0()
-> f64 {
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: f64 = 0.0;
    v___x_3796_ = lean_unsigned_to_nat(0);
    v___x_3797_ = lean_float_of_nat(v___x_3796_);
    return v___x_3797_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7(
    mut v_cls_3801_: *mut LeanObject,
    mut v_msg_3802_: *mut LeanObject,
    mut v___y_3803_: *mut LeanObject,
    mut v___y_3804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3824_: u8 = 0;
    let mut v_tid_3825_: u64 = 0;
    let mut v_traces_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3829_: u8 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: f64 = 0.0;
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3806_ = lean_ctor_get(v___y_3803_, 5);
                v___x_3807_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_isConstantReplacement_x3f_spec__0_spec__0_spec__1_spec__6_spec__10_spec__14_spec__16(v_msg_3802_, v___y_3803_, v___y_3804_);
                v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
                v_isSharedCheck_3852_ = (!lean_is_exclusive(v___x_3807_)) as u8;
                if v_isSharedCheck_3852_ == 0 {
                    v___x_3810_ = v___x_3807_;
                    v_isShared_3811_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3808_);
                    lean_dec(v___x_3807_);
                    v___x_3810_ = lean_box(0);
                    v_isShared_3811_ = v_isSharedCheck_3852_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3812_ = lean_st_ref_take(v___y_3804_);
                v_traceState_3813_ = lean_ctor_get(v___x_3812_, 4);
                v_env_3814_ = lean_ctor_get(v___x_3812_, 0);
                v_nextMacroScope_3815_ = lean_ctor_get(v___x_3812_, 1);
                v_ngen_3816_ = lean_ctor_get(v___x_3812_, 2);
                v_auxDeclNGen_3817_ = lean_ctor_get(v___x_3812_, 3);
                v_cache_3818_ = lean_ctor_get(v___x_3812_, 5);
                v_messages_3819_ = lean_ctor_get(v___x_3812_, 6);
                v_infoState_3820_ = lean_ctor_get(v___x_3812_, 7);
                v_snapshotTasks_3821_ = lean_ctor_get(v___x_3812_, 8);
                v_isSharedCheck_3851_ = (!lean_is_exclusive(v___x_3812_)) as u8;
                if v_isSharedCheck_3851_ == 0 {
                    v___x_3823_ = v___x_3812_;
                    v_isShared_3824_ = v_isSharedCheck_3851_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3821_);
                    lean_inc(v_infoState_3820_);
                    lean_inc(v_messages_3819_);
                    lean_inc(v_cache_3818_);
                    lean_inc(v_traceState_3813_);
                    lean_inc(v_auxDeclNGen_3817_);
                    lean_inc(v_ngen_3816_);
                    lean_inc(v_nextMacroScope_3815_);
                    lean_inc(v_env_3814_);
                    lean_dec(v___x_3812_);
                    v___x_3823_ = lean_box(0);
                    v_isShared_3824_ = v_isSharedCheck_3851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3825_ = lean_ctor_get_uint64(
                    v_traceState_3813_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3826_ = lean_ctor_get(v_traceState_3813_, 0);
                v_isSharedCheck_3850_ = (!lean_is_exclusive(v_traceState_3813_)) as u8;
                if v_isSharedCheck_3850_ == 0 {
                    v___x_3828_ = v_traceState_3813_;
                    v_isShared_3829_ = v_isSharedCheck_3850_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3826_);
                    lean_dec(v_traceState_3813_);
                    v___x_3828_ = lean_box(0);
                    v_isShared_3829_ = v_isSharedCheck_3850_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3830_ = lean_box(0);
                v___x_3831_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__0);
                v___x_3832_ = 0;
                v___x_3833_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1;
                v___x_3834_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3834_, 0, v_cls_3801_);
                lean_ctor_set(v___x_3834_, 1, v___x_3830_);
                lean_ctor_set(v___x_3834_, 2, v___x_3833_);
                lean_ctor_set_float(
                    v___x_3834_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3831_,
                );
                lean_ctor_set_float(
                    v___x_3834_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3831_,
                );
                lean_ctor_set_uint8(
                    v___x_3834_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3832_,
                );
                v___x_3835_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__2;
                v___x_3836_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3836_, 0, v___x_3834_);
                lean_ctor_set(v___x_3836_, 1, v_a_3808_);
                lean_ctor_set(v___x_3836_, 2, v___x_3835_);
                lean_inc(v_ref_3806_);
                v___x_3837_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3837_, 0, v_ref_3806_);
                lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                v___x_3838_ = l_Lean_PersistentArray_push___redArg(v_traces_3826_, v___x_3837_);
                if v_isShared_3829_ == 0 {
                    lean_ctor_set(v___x_3828_, 0, v___x_3838_);
                    v___x_3840_ = v___x_3828_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3838_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3849_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3825_,
                    );
                    v___x_3840_ = v_reuseFailAlloc_3849_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3824_ == 0 {
                    lean_ctor_set(v___x_3823_, 4, v___x_3840_);
                    v___x_3842_ = v___x_3823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_env_3814_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_nextMacroScope_3815_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_ngen_3816_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 3, v_auxDeclNGen_3817_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 4, v___x_3840_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 5, v_cache_3818_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 6, v_messages_3819_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 7, v_infoState_3820_);
                    lean_ctor_set(v_reuseFailAlloc_3848_, 8, v_snapshotTasks_3821_);
                    v___x_3842_ = v_reuseFailAlloc_3848_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3843_ = lean_st_ref_set(v___y_3804_, v___x_3842_);
                v___x_3844_ = lean_box(0);
                if v_isShared_3811_ == 0 {
                    lean_ctor_set(v___x_3810_, 0, v___x_3844_);
                    v___x_3846_ = v___x_3810_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3844_);
                    v___x_3846_ = v_reuseFailAlloc_3847_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___boxed(
    mut v_cls_3853_: *mut LeanObject,
    mut v_msg_3854_: *mut LeanObject,
    mut v___y_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3858_: *mut LeanObject = core::ptr::null_mut();
    v_res_3858_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7(v_cls_3853_, v_msg_3854_, v___y_3855_, v___y_3856_);
    lean_dec(v___y_3856_);
    lean_dec_ref(v___y_3855_);
    return v_res_3858_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    v___x_3861_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__1;
    v___x_3862_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__0;
    v___x_3863_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3862_, v___x_3861_);
    return v___x_3863_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6()
-> *mut LeanObject {
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    v___x_3868_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__5;
    v___x_3869_ = l_Lean_stringToMessageData(v___x_3868_);
    return v___x_3869_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8()
-> *mut LeanObject {
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    v___x_3871_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__7;
    v___x_3872_ = l_Lean_stringToMessageData(v___x_3871_);
    return v___x_3872_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9()
-> *mut LeanObject {
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    v___x_3873_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7___closed__1;
    v___x_3874_ = l_Lean_stringToMessageData(v___x_3873_);
    return v___x_3874_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12()
-> *mut LeanObject {
    let mut v_cls_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    v_cls_3878_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4;
    v___x_3879_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__11;
    v___x_3880_ = l_Lean_Name_append(v___x_3879_, v_cls_3878_);
    return v___x_3880_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14()
-> *mut LeanObject {
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    v___x_3882_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__13;
    v___x_3883_ = l_Lean_stringToMessageData(v___x_3882_);
    return v___x_3883_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16()
-> *mut LeanObject {
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    v___x_3885_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__15;
    v___x_3886_ = l_Lean_stringToMessageData(v___x_3885_);
    return v___x_3886_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(
    mut v_mod_3891_: *mut LeanObject,
    mut v_isMeta_3892_: u8,
    mut v_hint_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3899_: u8 = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3921_: u8 = 0;
    let mut v_asyncMode_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_unused_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v_options_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3936_: u8 = 0;
    let mut v_inheritedTraceOptions_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3897_ = lean_st_ref_get(v___y_3895_);
                v_env_3898_ = lean_ctor_get(v___x_3897_, 0);
                lean_inc_ref(v_env_3898_);
                lean_dec(v___x_3897_);
                v_isExporting_3899_ = lean_ctor_get_uint8(
                    v_env_3898_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_3898_);
                v___x_3900_ = lean_st_ref_get(v___y_3895_);
                v_env_3901_ = lean_ctor_get(v___x_3900_, 0);
                lean_inc_ref(v_env_3901_);
                lean_dec(v___x_3900_);
                v___x_3902_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__2);
                lean_inc(v_mod_3891_);
                v_entry_3903_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_3903_, 0, v_mod_3891_);
                lean_ctor_set_uint8(
                    v_entry_3903_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_3899_,
                );
                lean_ctor_set_uint8(
                    v_entry_3903_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_3892_,
                );
                v___x_3904_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_3905_ = lean_box(1);
                v___x_3906_ = lean_box(0);
                v___x_3933_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3902_,
                    v___x_3904_,
                    v_env_3901_,
                    v___x_3905_,
                    v___x_3906_,
                );
                v___x_3934_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(v___x_3933_, v_entry_3903_);
                lean_dec(v___x_3933_);
                if v___x_3934_ == 0 {
                    v_options_3935_ = lean_ctor_get(v___y_3894_, 2);
                    v_hasTrace_3936_ = lean_ctor_get_uint8(
                        v_options_3935_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3936_ == 0 {
                        lean_dec(v_hint_3893_);
                        lean_dec(v_mod_3891_);
                        v___y_3908_ = v___y_3895_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3937_ = lean_ctor_get(v___y_3894_, 13);
                        v_cls_3938_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__4;
                        v___x_3958_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__12);
                        v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3937_,
                            v_options_3935_,
                            v___x_3958_,
                        );
                        if v___x_3959_ == 0 {
                            lean_dec(v_hint_3893_);
                            lean_dec(v_mod_3891_);
                            v___y_3908_ = v___y_3895_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3960_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__14);
                            if v_isExporting_3899_ == 0 {
                                v___x_3969_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__19;
                                v___y_3962_ = v___x_3969_;
                                state = 6;
                                continue;
                            } else {
                                v___x_3970_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__20;
                                v___y_3962_ = v___x_3970_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v_entry_3903_, 1);
                    lean_dec(v_hint_3893_);
                    lean_dec(v_mod_3891_);
                    v___x_3971_ = lean_box(0);
                    v___x_3972_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3972_, 0, v___x_3971_);
                    return v___x_3972_;
                }
            }
            1 => {
                v___x_3909_ = lean_st_ref_take(v___y_3908_);
                v_toEnvExtension_3910_ = lean_ctor_get(v___x_3904_, 0);
                v_env_3911_ = lean_ctor_get(v___x_3909_, 0);
                v_nextMacroScope_3912_ = lean_ctor_get(v___x_3909_, 1);
                v_ngen_3913_ = lean_ctor_get(v___x_3909_, 2);
                v_auxDeclNGen_3914_ = lean_ctor_get(v___x_3909_, 3);
                v_traceState_3915_ = lean_ctor_get(v___x_3909_, 4);
                v_messages_3916_ = lean_ctor_get(v___x_3909_, 6);
                v_infoState_3917_ = lean_ctor_get(v___x_3909_, 7);
                v_snapshotTasks_3918_ = lean_ctor_get(v___x_3909_, 8);
                v_isSharedCheck_3931_ = (!lean_is_exclusive(v___x_3909_)) as u8;
                if v_isSharedCheck_3931_ == 0 {
                    v_unused_3932_ = lean_ctor_get(v___x_3909_, 5);
                    lean_dec(v_unused_3932_);
                    v___x_3920_ = v___x_3909_;
                    v_isShared_3921_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3918_);
                    lean_inc(v_infoState_3917_);
                    lean_inc(v_messages_3916_);
                    lean_inc(v_traceState_3915_);
                    lean_inc(v_auxDeclNGen_3914_);
                    lean_inc(v_ngen_3913_);
                    lean_inc(v_nextMacroScope_3912_);
                    lean_inc(v_env_3911_);
                    lean_dec(v___x_3909_);
                    v___x_3920_ = lean_box(0);
                    v_isShared_3921_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_3922_ = lean_ctor_get(v_toEnvExtension_3910_, 2);
                v___x_3923_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3904_,
                    v_env_3911_,
                    v_entry_3903_,
                    v_asyncMode_3922_,
                    v___x_3906_,
                );
                v___x_3924_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Compiler_CSimp_add_spec__0___redArg___closed__2);
                if v_isShared_3921_ == 0 {
                    lean_ctor_set(v___x_3920_, 5, v___x_3924_);
                    lean_ctor_set(v___x_3920_, 0, v___x_3923_);
                    v___x_3926_ = v___x_3920_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3923_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_nextMacroScope_3912_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_ngen_3913_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_auxDeclNGen_3914_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 4, v_traceState_3915_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 5, v___x_3924_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 6, v_messages_3916_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 7, v_infoState_3917_);
                    lean_ctor_set(v_reuseFailAlloc_3930_, 8, v_snapshotTasks_3918_);
                    v___x_3926_ = v_reuseFailAlloc_3930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3927_ = lean_st_ref_set(v___y_3908_, v___x_3926_);
                v___x_3928_ = lean_box(0);
                v___x_3929_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                return v___x_3929_;
            }
            4 => {
                v___x_3942_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3942_, 0, v___y_3940_);
                lean_ctor_set(v___x_3942_, 1, v___y_3941_);
                v___x_3943_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__7(v_cls_3938_, v___x_3942_, v___y_3894_, v___y_3895_);
                if lean_obj_tag(v___x_3943_) == 0 {
                    lean_dec_ref_known(v___x_3943_, 1);
                    v___y_3908_ = v___y_3895_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_3903_, 1);
                    return v___x_3943_;
                }
            }
            5 => {
                lean_inc_ref(v___y_3946_);
                v___x_3947_ = l_Lean_stringToMessageData(v___y_3946_);
                v___x_3948_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3948_, 0, v___y_3945_);
                lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__6);
                v___x_3950_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                v___x_3951_ = l_Lean_MessageData_ofName(v_mod_3891_);
                v___x_3952_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3952_, 0, v___x_3950_);
                lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                v___x_3953_ = l_Lean_Name_isAnonymous(v_hint_3893_);
                if v___x_3953_ == 0 {
                    v___x_3954_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__8);
                    v___x_3955_ = l_Lean_MessageData_ofName(v_hint_3893_);
                    v___x_3956_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3956_, 0, v___x_3954_);
                    lean_ctor_set(v___x_3956_, 1, v___x_3955_);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3956_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_3893_);
                    v___x_3957_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__9);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3957_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_3962_);
                v___x_3963_ = l_Lean_stringToMessageData(v___y_3962_);
                v___x_3964_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3964_, 0, v___x_3960_);
                lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                v___x_3965_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__16);
                v___x_3966_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3966_, 0, v___x_3964_);
                lean_ctor_set(v___x_3966_, 1, v___x_3965_);
                if v_isMeta_3892_ == 0 {
                    v___x_3967_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__17;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3967_;
                    state = 5;
                    continue;
                } else {
                    v___x_3968_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___closed__18;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3968_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3___boxed(
    mut v_mod_3973_: *mut LeanObject,
    mut v_isMeta_3974_: *mut LeanObject,
    mut v_hint_3975_: *mut LeanObject,
    mut v___y_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3979_: u8 = 0;
    let mut v_res_3980_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3979_ = (lean_unbox(v_isMeta_3974_) as u8);
    v_res_3980_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(v_mod_3973_, v_isMeta_boxed_3979_, v_hint_3975_, v___y_3976_, v___y_3977_);
    lean_dec(v___y_3977_);
    lean_dec_ref(v___y_3976_);
    return v_res_3980_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4(
    mut v___x_3981_: *mut LeanObject,
    mut v_declName_3982_: *mut LeanObject,
    mut v_as_3983_: *mut LeanObject,
    mut v_sz_3984_: usize,
    mut v_i_3985_: usize,
    mut v_b_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3990_: u8 = 0;
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: u8 = 0;
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: usize = 0;
    let mut v___x_4003_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3990_ = lean_usize_dec_lt(v_i_3985_, v_sz_3984_);
                if v___x_3990_ == 0 {
                    lean_dec(v_declName_3982_);
                    v___x_3991_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3991_, 0, v_b_3986_);
                    return v___x_3991_;
                } else {
                    v___x_3992_ = l_Lean_Environment_header(v___x_3981_);
                    v_modules_3993_ = lean_ctor_get(v___x_3992_, 3);
                    lean_inc_ref(v_modules_3993_);
                    lean_dec_ref(v___x_3992_);
                    v___x_3994_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_3995_ = lean_array_uget_borrowed(v_as_3983_, v_i_3985_);
                    v___x_3996_ = lean_array_get(v___x_3994_, v_modules_3993_, v_a_3995_);
                    lean_dec_ref(v_modules_3993_);
                    v_toImport_3997_ = lean_ctor_get(v___x_3996_, 0);
                    lean_inc_ref(v_toImport_3997_);
                    lean_dec(v___x_3996_);
                    v_module_3998_ = lean_ctor_get(v_toImport_3997_, 0);
                    lean_inc(v_module_3998_);
                    lean_dec_ref(v_toImport_3997_);
                    v___x_3999_ = 0;
                    lean_inc(v_declName_3982_);
                    v___x_4000_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(v_module_3998_, v___x_3999_, v_declName_3982_, v___y_3987_, v___y_3988_);
                    if lean_obj_tag(v___x_4000_) == 0 {
                        lean_dec_ref_known(v___x_4000_, 1);
                        v___x_4001_ = lean_box(0);
                        v___x_4002_ = 1usize;
                        v___x_4003_ = lean_usize_add(v_i_3985_, v___x_4002_);
                        v_i_3985_ = v___x_4003_;
                        v_b_3986_ = v___x_4001_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_3982_);
                        return v___x_4000_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4___boxed(
    mut v___x_4005_: *mut LeanObject,
    mut v_declName_4006_: *mut LeanObject,
    mut v_as_4007_: *mut LeanObject,
    mut v_sz_4008_: *mut LeanObject,
    mut v_i_4009_: *mut LeanObject,
    mut v_b_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4014_: usize = 0;
    let mut v_i_boxed_4015_: usize = 0;
    let mut v_res_4016_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4014_ = lean_unbox_usize(v_sz_4008_);
    lean_dec(v_sz_4008_);
    v_i_boxed_4015_ = lean_unbox_usize(v_i_4009_);
    lean_dec(v_i_4009_);
    v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4(v___x_4005_, v_declName_4006_, v_as_4007_, v_sz_boxed_4014_, v_i_boxed_4015_, v_b_4010_, v___y_4011_, v___y_4012_);
    lean_dec(v___y_4012_);
    lean_dec_ref(v___y_4011_);
    lean_dec_ref(v_as_4007_);
    lean_dec_ref(v___x_4005_);
    return v_res_4016_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    v___x_4019_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__1;
    v___x_4020_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__0;
    v___x_4021_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_4020_, v___x_4019_);
    return v___x_4021_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1(
    mut v_declName_4024_: *mut LeanObject,
    mut v_isMeta_4025_: u8,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4037_: usize = 0;
    let mut v___x_4038_: usize = 0;
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4042_: u8 = 0;
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4046_: u8 = 0;
    let mut v_unused_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4059_: u8 = 0;
    let mut v_toImport_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: u8 = 0;
    let mut v___x_4071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4029_ = lean_st_ref_get(v___y_4027_);
                v_env_4033_ = lean_ctor_get(v___x_4029_, 0);
                lean_inc_ref(v_env_4033_);
                lean_dec(v___x_4029_);
                v___x_4048_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4033_, v_declName_4024_);
                if lean_obj_tag(v___x_4048_) == 0 {
                    lean_dec_ref(v_env_4033_);
                    lean_dec(v_declName_4024_);
                    state = 1;
                    continue;
                } else {
                    v_val_4049_ = lean_ctor_get(v___x_4048_, 0);
                    lean_inc(v_val_4049_);
                    lean_dec_ref_known(v___x_4048_, 1);
                    v___x_4050_ = l_Lean_Environment_header(v_env_4033_);
                    v_modules_4051_ = lean_ctor_get(v___x_4050_, 3);
                    lean_inc_ref(v_modules_4051_);
                    lean_dec_ref(v___x_4050_);
                    v___x_4052_ = lean_array_get_size(v_modules_4051_);
                    v___x_4053_ = lean_nat_dec_lt(v_val_4049_, v___x_4052_);
                    if v___x_4053_ == 0 {
                        lean_dec_ref(v_modules_4051_);
                        lean_dec(v_val_4049_);
                        lean_dec_ref(v_env_4033_);
                        lean_dec(v_declName_4024_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4054_ = lean_st_ref_get(v___y_4027_);
                        v_env_4055_ = lean_ctor_get(v___x_4054_, 0);
                        lean_inc_ref(v_env_4055_);
                        lean_dec(v___x_4054_);
                        v___x_4056_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__2);
                        v___x_4057_ = lean_array_fget(v_modules_4051_, v_val_4049_);
                        lean_dec(v_val_4049_);
                        lean_dec_ref(v_modules_4051_);
                        if v_isMeta_4025_ == 0 {
                            lean_dec_ref(v_env_4055_);
                            v___y_4059_ = v_isMeta_4025_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_4024_);
                            v___x_4070_ = l_Lean_isMarkedMeta(v_env_4055_, v_declName_4024_);
                            if v___x_4070_ == 0 {
                                v___y_4059_ = v_isMeta_4025_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4071_ = 0;
                                v___y_4059_ = v___x_4071_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4031_ = lean_box(0);
                v___x_4032_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4032_, 0, v___x_4031_);
                return v___x_4032_;
            }
            2 => {
                v___x_4036_ = lean_box(0);
                v_sz_4037_ = lean_array_size(v___y_4035_);
                v___x_4038_ = 0usize;
                v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__4(v_env_4033_, v_declName_4024_, v___y_4035_, v_sz_4037_, v___x_4038_, v___x_4036_, v___y_4026_, v___y_4027_);
                lean_dec_ref(v___y_4035_);
                lean_dec_ref(v_env_4033_);
                if lean_obj_tag(v___x_4039_) == 0 {
                    v_isSharedCheck_4046_ = (!lean_is_exclusive(v___x_4039_)) as u8;
                    if v_isSharedCheck_4046_ == 0 {
                        v_unused_4047_ = lean_ctor_get(v___x_4039_, 0);
                        lean_dec(v_unused_4047_);
                        v___x_4041_ = v___x_4039_;
                        v_isShared_4042_ = v_isSharedCheck_4046_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_4039_);
                        v___x_4041_ = lean_box(0);
                        v_isShared_4042_ = v_isSharedCheck_4046_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4039_;
                }
            }
            3 => {
                if v_isShared_4042_ == 0 {
                    lean_ctor_set(v___x_4041_, 0, v___x_4036_);
                    v___x_4044_ = v___x_4041_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4036_);
                    v___x_4044_ = v_reuseFailAlloc_4045_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4044_;
            }
            5 => {
                v_toImport_4060_ = lean_ctor_get(v___x_4057_, 0);
                lean_inc_ref(v_toImport_4060_);
                lean_dec(v___x_4057_);
                v_module_4061_ = lean_ctor_get(v_toImport_4060_, 0);
                lean_inc(v_module_4061_);
                lean_dec_ref(v_toImport_4060_);
                lean_inc(v_declName_4024_);
                v___x_4062_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3(v_module_4061_, v___y_4059_, v_declName_4024_, v___y_4026_, v___y_4027_);
                if lean_obj_tag(v___x_4062_) == 0 {
                    lean_dec_ref_known(v___x_4062_, 1);
                    v___x_4063_ = l_Lean_indirectModUseExt;
                    v___x_4064_ = lean_box(1);
                    v___x_4065_ = lean_box(0);
                    lean_inc_ref(v_env_4033_);
                    v___x_4066_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4056_,
                        v___x_4063_,
                        v_env_4033_,
                        v___x_4064_,
                        v___x_4065_,
                    );
                    v___x_4067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v___x_4066_, v_declName_4024_);
                    lean_dec(v___x_4066_);
                    if lean_obj_tag(v___x_4067_) == 0 {
                        v___x_4068_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___closed__3;
                        v___y_4035_ = v___x_4068_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4069_ = lean_ctor_get(v___x_4067_, 0);
                        lean_inc(v_val_4069_);
                        lean_dec_ref_known(v___x_4067_, 1);
                        v___y_4035_ = v_val_4069_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_4033_);
                    lean_dec(v_declName_4024_);
                    return v___x_4062_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___boxed(
    mut v_declName_4072_: *mut LeanObject,
    mut v_isMeta_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
    mut v___y_4075_: *mut LeanObject,
    mut v___y_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_4077_: u8 = 0;
    let mut v_res_4078_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4077_ = (lean_unbox(v_isMeta_4073_) as u8);
    v_res_4078_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1(
            v_declName_4072_,
            v_isMeta_boxed_4077_,
            v___y_4074_,
            v___y_4075_,
        );
    lean_dec(v___y_4075_);
    lean_dec_ref(v___y_4074_);
    return v_res_4078_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_keys_4079_: *mut LeanObject,
    mut v_vals_4080_: *mut LeanObject,
    mut v_i_4081_: *mut LeanObject,
    mut v_k_4082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4083_ = lean_array_get_size(v_keys_4079_);
                v___x_4084_ = lean_nat_dec_lt(v_i_4081_, v___x_4083_);
                if v___x_4084_ == 0 {
                    lean_dec(v_i_4081_);
                    v___x_4085_ = lean_box(0);
                    return v___x_4085_;
                } else {
                    v_k_x27_4086_ = lean_array_fget_borrowed(v_keys_4079_, v_i_4081_);
                    v___x_4087_ = lean_name_eq(v_k_4082_, v_k_x27_4086_);
                    if v___x_4087_ == 0 {
                        v___x_4088_ = lean_unsigned_to_nat(1);
                        v___x_4089_ = lean_nat_add(v_i_4081_, v___x_4088_);
                        lean_dec(v_i_4081_);
                        v_i_4081_ = v___x_4089_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4091_ = lean_array_fget_borrowed(v_vals_4080_, v_i_4081_);
                        lean_dec(v_i_4081_);
                        lean_inc(v___x_4091_);
                        v___x_4092_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4092_, 0, v___x_4091_);
                        return v___x_4092_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_keys_4093_: *mut LeanObject,
    mut v_vals_4094_: *mut LeanObject,
    mut v_i_4095_: *mut LeanObject,
    mut v_k_4096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4097_: *mut LeanObject = core::ptr::null_mut();
    v_res_4097_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_4093_, v_vals_4094_, v_i_4095_, v_k_4096_);
    lean_dec(v_k_4096_);
    lean_dec_ref(v_vals_4094_);
    lean_dec_ref(v_keys_4093_);
    return v_res_4097_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_x_4098_: *mut LeanObject,
    mut v_x_4099_: usize,
    mut v_x_4100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: usize = 0;
    let mut v___x_4104_: usize = 0;
    let mut v___x_4105_: usize = 0;
    let mut v_j_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: usize = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4098_) == 0 {
                    v_es_4101_ = lean_ctor_get(v_x_4098_, 0);
                    v___x_4102_ = lean_box(2);
                    v___x_4103_ = 5usize;
                    v___x_4104_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4105_ = lean_usize_land(v_x_4099_, v___x_4104_);
                    v_j_4106_ = lean_usize_to_nat(v___x_4105_);
                    v___x_4107_ = lean_array_get_borrowed(v___x_4102_, v_es_4101_, v_j_4106_);
                    lean_dec(v_j_4106_);
                    match lean_obj_tag(v___x_4107_) {
                        0 => {
                            v_key_4108_ = lean_ctor_get(v___x_4107_, 0);
                            v_val_4109_ = lean_ctor_get(v___x_4107_, 1);
                            v___x_4110_ = lean_name_eq(v_x_4100_, v_key_4108_);
                            if v___x_4110_ == 0 {
                                v___x_4111_ = lean_box(0);
                                return v___x_4111_;
                            } else {
                                lean_inc(v_val_4109_);
                                v___x_4112_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4112_, 0, v_val_4109_);
                                return v___x_4112_;
                            }
                        }
                        1 => {
                            v_node_4113_ = lean_ctor_get(v___x_4107_, 0);
                            v___x_4114_ = lean_usize_shift_right(v_x_4099_, v___x_4103_);
                            v_x_4098_ = v_node_4113_;
                            v_x_4099_ = v___x_4114_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4116_ = lean_box(0);
                            return v___x_4116_;
                        }
                    }
                } else {
                    v_ks_4117_ = lean_ctor_get(v_x_4098_, 0);
                    v_vs_4118_ = lean_ctor_get(v_x_4098_, 1);
                    v___x_4119_ = lean_unsigned_to_nat(0);
                    v___x_4120_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_4117_, v_vs_4118_, v___x_4119_, v_x_4100_);
                    return v___x_4120_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4121_: *mut LeanObject,
    mut v_x_4122_: *mut LeanObject,
    mut v_x_4123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5639__boxed_4124_: usize = 0;
    let mut v_res_4125_: *mut LeanObject = core::ptr::null_mut();
    v_x_5639__boxed_4124_ = lean_unbox_usize(v_x_4122_);
    lean_dec(v_x_4122_);
    v_res_4125_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(v_x_4121_, v_x_5639__boxed_4124_, v_x_4123_);
    lean_dec(v_x_4123_);
    lean_dec_ref(v_x_4121_);
    return v_res_4125_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(
    mut v_x_4126_: *mut LeanObject,
    mut v_x_4127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4129_: u64 = 0;
    let mut v___x_4130_: usize = 0;
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: u64 = 0;
    let mut v_hash_4133_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4127_) == 0 {
                    v___x_4132_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_4129_ = v___x_4132_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4133_ = lean_ctor_get_uint64(
                        v_x_4127_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4129_ = v_hash_4133_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4130_ = lean_uint64_to_usize(v___y_4129_);
                v___x_4131_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(v_x_4126_, v___x_4130_, v_x_4127_);
                return v___x_4131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_4134_: *mut LeanObject,
    mut v_x_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4136_: *mut LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(v_x_4134_, v_x_4135_);
    lean_dec(v_x_4135_);
    lean_dec_ref(v_x_4134_);
    return v_res_4136_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(
    mut v_x_4137_: *mut LeanObject,
    mut v_x_4138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_4139_: u8 = 0;
    v_stage_u2081_4139_ = lean_ctor_get_uint8(
        v_x_4137_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_4139_ == 0 {
        let mut v_map_u2081_4140_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_4141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_4140_ = lean_ctor_get(v_x_4137_, 0);
        v_map_u2082_4141_ = lean_ctor_get(v_x_4137_, 1);
        v___x_4142_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(v_map_u2082_4141_, v_x_4138_);
        if lean_obj_tag(v___x_4142_) == 0 {
            let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
            v___x_4143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_map_u2081_4140_, v_x_4138_);
            return v___x_4143_;
        } else {
            return v___x_4142_;
        }
    } else {
        let mut v_map_u2081_4144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_4144_ = lean_ctor_get(v_x_4137_, 0);
        v___x_4145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_map_u2081_4144_, v_x_4138_);
        return v___x_4145_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg___boxed(
    mut v_x_4146_: *mut LeanObject,
    mut v_x_4147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4148_: *mut LeanObject = core::ptr::null_mut();
    v_res_4148_ =
        l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(
            v_x_4146_, v_x_4147_,
        );
    lean_dec(v_x_4147_);
    lean_dec_ref(v_x_4146_);
    return v_res_4148_;
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant_x3f(
    mut v_env_4149_: *mut LeanObject,
    mut v_e_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
    mut v_a_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4166_: u8 = 0;
    let mut v_toDeclName_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmName_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: u8 = 0;
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v_unused_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4194_: u8 = 0;
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_4150_) == 4 {
                    v_declName_4154_ = lean_ctor_get(v_e_4150_, 0);
                    v___x_4155_ = l_Lean_Compiler_CSimp_ext;
                    v_ext_4156_ = lean_ctor_get(v___x_4155_, 1);
                    v_toEnvExtension_4157_ = lean_ctor_get(v_ext_4156_, 0);
                    v_asyncMode_4158_ = lean_ctor_get(v_toEnvExtension_4157_, 2);
                    v___x_4159_ = l_Lean_Compiler_CSimp_instInhabitedState_default;
                    v_s_4160_ = l_Lean_ScopedEnvExtension_getState___redArg(
                        v___x_4159_,
                        v___x_4155_,
                        v_env_4149_,
                        v_asyncMode_4158_,
                    );
                    v_map_4161_ = lean_ctor_get(v_s_4160_, 0);
                    lean_inc_ref(v_map_4161_);
                    lean_dec(v_s_4160_);
                    v___x_4162_ = l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(v_map_4161_, v_declName_4154_);
                    lean_dec_ref(v_map_4161_);
                    if lean_obj_tag(v___x_4162_) == 1 {
                        v_val_4163_ = lean_ctor_get(v___x_4162_, 0);
                        v_isSharedCheck_4195_ = (!lean_is_exclusive(v___x_4162_)) as u8;
                        if v_isSharedCheck_4195_ == 0 {
                            v___x_4165_ = v___x_4162_;
                            v_isShared_4166_ = v_isSharedCheck_4195_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_4163_);
                            lean_dec(v___x_4162_);
                            v___x_4165_ = lean_box(0);
                            v_isShared_4166_ = v_isSharedCheck_4195_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4162_);
                        v___x_4196_ = lean_box(0);
                        v___x_4197_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4197_, 0, v___x_4196_);
                        return v___x_4197_;
                    }
                } else {
                    lean_dec_ref(v_env_4149_);
                    v___x_4198_ = lean_box(0);
                    v___x_4199_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4199_, 0, v___x_4198_);
                    return v___x_4199_;
                }
            }
            1 => {
                v_toDeclName_4167_ = lean_ctor_get(v_val_4163_, 1);
                lean_inc(v_toDeclName_4167_);
                v_thmName_4168_ = lean_ctor_get(v_val_4163_, 2);
                lean_inc(v_thmName_4168_);
                lean_dec(v_val_4163_);
                v___x_4169_ = 0;
                v___x_4170_ = lean_box((v___x_4169_) as usize);
                v___x_4171_ = lean_alloc_closure(l_Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1___boxed as *mut core::ffi::c_void, 5, 2);
                lean_closure_set(v___x_4171_, 0, v_thmName_4168_);
                lean_closure_set(v___x_4171_, 1, v___x_4170_);
                v___x_4172_ = 1;
                v___x_4173_ = l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(v___x_4171_, v___x_4172_, v_a_4151_, v_a_4152_);
                if lean_obj_tag(v___x_4173_) == 0 {
                    v_isSharedCheck_4185_ = (!lean_is_exclusive(v___x_4173_)) as u8;
                    if v_isSharedCheck_4185_ == 0 {
                        v_unused_4186_ = lean_ctor_get(v___x_4173_, 0);
                        lean_dec(v_unused_4186_);
                        v___x_4175_ = v___x_4173_;
                        v_isShared_4176_ = v_isSharedCheck_4185_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_4173_);
                        v___x_4175_ = lean_box(0);
                        v_isShared_4176_ = v_isSharedCheck_4185_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_toDeclName_4167_);
                    lean_del_object(v___x_4165_);
                    v_a_4187_ = lean_ctor_get(v___x_4173_, 0);
                    v_isSharedCheck_4194_ = (!lean_is_exclusive(v___x_4173_)) as u8;
                    if v_isSharedCheck_4194_ == 0 {
                        v___x_4189_ = v___x_4173_;
                        v_isShared_4190_ = v_isSharedCheck_4194_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4187_);
                        lean_dec(v___x_4173_);
                        v___x_4189_ = lean_box(0);
                        v_isShared_4190_ = v_isSharedCheck_4194_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4177_ = l_Lean_Expr_constLevels_x21(v_e_4150_);
                v___x_4178_ = l_Lean_mkConst(v_toDeclName_4167_, v___x_4177_);
                if v_isShared_4166_ == 0 {
                    lean_ctor_set(v___x_4165_, 0, v___x_4178_);
                    v___x_4180_ = v___x_4165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4178_);
                    v___x_4180_ = v_reuseFailAlloc_4184_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4176_ == 0 {
                    lean_ctor_set(v___x_4175_, 0, v___x_4180_);
                    v___x_4182_ = v___x_4175_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4180_);
                    v___x_4182_ = v_reuseFailAlloc_4183_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4182_;
            }
            5 => {
                if v_isShared_4190_ == 0 {
                    v___x_4192_ = v___x_4189_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
                    v___x_4192_ = v_reuseFailAlloc_4193_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant_x3f___boxed(
    mut v_env_4200_: *mut LeanObject,
    mut v_e_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4205_: *mut LeanObject = core::ptr::null_mut();
    v_res_4205_ =
        l_Lean_Compiler_CSimp_replaceConstant_x3f(v_env_4200_, v_e_4201_, v_a_4202_, v_a_4203_);
    lean_dec(v_a_4203_);
    lean_dec_ref(v_a_4202_);
    lean_dec_ref(v_e_4201_);
    return v_res_4205_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0(
    mut v_00_u03b2_4206_: *mut LeanObject,
    mut v_x_4207_: *mut LeanObject,
    mut v_x_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    v___x_4209_ =
        l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___redArg(
            v_x_4207_, v_x_4208_,
        );
    return v___x_4209_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0___boxed(
    mut v_00_u03b2_4210_: *mut LeanObject,
    mut v_x_4211_: *mut LeanObject,
    mut v_x_4212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4213_: *mut LeanObject = core::ptr::null_mut();
    v_res_4213_ = l_Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0(
        v_00_u03b2_4210_,
        v_x_4211_,
        v_x_4212_,
    );
    lean_dec(v_x_4212_);
    lean_dec_ref(v_x_4211_);
    return v_res_4213_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6(
    mut v_00_u03b1_4214_: *mut LeanObject,
    mut v_x_4215_: *mut LeanObject,
    mut v_isExporting_4216_: u8,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    v___x_4220_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___redArg(v_x_4215_, v_isExporting_4216_, v___y_4217_, v___y_4218_);
    return v___x_4220_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6___boxed(
    mut v_00_u03b1_4221_: *mut LeanObject,
    mut v_x_4222_: *mut LeanObject,
    mut v_isExporting_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4227_: u8 = 0;
    let mut v_res_4228_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4227_ = (lean_unbox(v_isExporting_4223_) as u8);
    v_res_4228_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2_spec__6(v_00_u03b1_4221_, v_x_4222_, v_isExporting_boxed_4227_, v___y_4224_, v___y_4225_);
    lean_dec(v___y_4225_);
    lean_dec_ref(v___y_4224_);
    return v_res_4228_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2(
    mut v_00_u03b1_4229_: *mut LeanObject,
    mut v_x_4230_: *mut LeanObject,
    mut v_when_4231_: u8,
    mut v___y_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    v___x_4235_ =
        l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___redArg(
            v_x_4230_,
            v_when_4231_,
            v___y_4232_,
            v___y_4233_,
        );
    return v___x_4235_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2___boxed(
    mut v_00_u03b1_4236_: *mut LeanObject,
    mut v_x_4237_: *mut LeanObject,
    mut v_when_4238_: *mut LeanObject,
    mut v___y_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
    mut v___y_4241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_4242_: u8 = 0;
    let mut v_res_4243_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_4242_ = (lean_unbox(v_when_4238_) as u8);
    v_res_4243_ = l_Lean_withoutExporting___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__2(
        v_00_u03b1_4236_,
        v_x_4237_,
        v_when_boxed_4242_,
        v___y_4239_,
        v___y_4240_,
    );
    lean_dec(v___y_4240_);
    lean_dec_ref(v___y_4239_);
    return v_res_4243_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0(
    mut v_00_u03b2_4244_: *mut LeanObject,
    mut v_x_4245_: *mut LeanObject,
    mut v_x_4246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___redArg(v_x_4245_, v_x_4246_);
    return v___x_4247_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_4248_: *mut LeanObject,
    mut v_x_4249_: *mut LeanObject,
    mut v_x_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4251_: *mut LeanObject = core::ptr::null_mut();
    v_res_4251_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0(v_00_u03b2_4248_, v_x_4249_, v_x_4250_);
    lean_dec(v_x_4250_);
    lean_dec_ref(v_x_4249_);
    return v_res_4251_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1(
    mut v_00_u03b2_4252_: *mut LeanObject,
    mut v_m_4253_: *mut LeanObject,
    mut v_a_4254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    v___x_4255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___redArg(v_m_4253_, v_a_4254_);
    return v___x_4255_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1___boxed(
    mut v_00_u03b2_4256_: *mut LeanObject,
    mut v_m_4257_: *mut LeanObject,
    mut v_a_4258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4259_: *mut LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1(v_00_u03b2_4256_, v_m_4257_, v_a_4258_);
    lean_dec(v_a_4258_);
    lean_dec_ref(v_m_4257_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4260_: *mut LeanObject,
    mut v_x_4261_: *mut LeanObject,
    mut v_x_4262_: usize,
    mut v_x_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    v___x_4264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___redArg(v_x_4261_, v_x_4262_, v_x_4263_);
    return v___x_4264_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4265_: *mut LeanObject,
    mut v_x_4266_: *mut LeanObject,
    mut v_x_4267_: *mut LeanObject,
    mut v_x_4268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5851__boxed_4269_: usize = 0;
    let mut v_res_4270_: *mut LeanObject = core::ptr::null_mut();
    v_x_5851__boxed_4269_ = lean_unbox_usize(v_x_4267_);
    lean_dec(v_x_4267_);
    v_res_4270_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1(v_00_u03b2_4265_, v_x_4266_, v_x_5851__boxed_4269_, v_x_4268_);
    lean_dec(v_x_4268_);
    lean_dec_ref(v_x_4266_);
    return v_res_4270_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3(
    mut v_00_u03b2_4271_: *mut LeanObject,
    mut v_a_4272_: *mut LeanObject,
    mut v_x_4273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    v___x_4274_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___redArg(v_a_4272_, v_x_4273_);
    return v___x_4274_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_4275_: *mut LeanObject,
    mut v_a_4276_: *mut LeanObject,
    mut v_x_4277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4278_: *mut LeanObject = core::ptr::null_mut();
    v_res_4278_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__1_spec__3(v_00_u03b2_4275_, v_a_4276_, v_x_4277_);
    lean_dec(v_x_4277_);
    lean_dec(v_a_4276_);
    return v_res_4278_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6(
    mut v_00_u03b2_4279_: *mut LeanObject,
    mut v_x_4280_: *mut LeanObject,
    mut v_x_4281_: *mut LeanObject,
) -> u8 {
    let mut v___x_4282_: u8 = 0;
    v___x_4282_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___redArg(v_x_4280_, v_x_4281_);
    return v___x_4282_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_4283_: *mut LeanObject,
    mut v_x_4284_: *mut LeanObject,
    mut v_x_4285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4286_: u8 = 0;
    let mut v_r_4287_: *mut LeanObject = core::ptr::null_mut();
    v_res_4286_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6(v_00_u03b2_4283_, v_x_4284_, v_x_4285_);
    lean_dec_ref(v_x_4285_);
    lean_dec_ref(v_x_4284_);
    v_r_4287_ = lean_box((v_res_4286_) as usize);
    return v_r_4287_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4288_: *mut LeanObject,
    mut v_keys_4289_: *mut LeanObject,
    mut v_vals_4290_: *mut LeanObject,
    mut v_heq_4291_: *mut LeanObject,
    mut v_i_4292_: *mut LeanObject,
    mut v_k_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_4289_, v_vals_4290_, v_i_4292_, v_k_4293_);
    return v___x_4294_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_4295_: *mut LeanObject,
    mut v_keys_4296_: *mut LeanObject,
    mut v_vals_4297_: *mut LeanObject,
    mut v_heq_4298_: *mut LeanObject,
    mut v_i_4299_: *mut LeanObject,
    mut v_k_4300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4301_: *mut LeanObject = core::ptr::null_mut();
    v_res_4301_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_4295_, v_keys_4296_, v_vals_4297_, v_heq_4298_, v_i_4299_, v_k_4300_);
    lean_dec(v_k_4300_);
    lean_dec_ref(v_vals_4297_);
    lean_dec_ref(v_keys_4296_);
    return v_res_4301_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10(
    mut v_00_u03b2_4302_: *mut LeanObject,
    mut v_x_4303_: *mut LeanObject,
    mut v_x_4304_: usize,
    mut v_x_4305_: *mut LeanObject,
) -> u8 {
    let mut v___x_4306_: u8 = 0;
    v___x_4306_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___redArg(v_x_4303_, v_x_4304_, v_x_4305_);
    return v___x_4306_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10___boxed(
    mut v_00_u03b2_4307_: *mut LeanObject,
    mut v_x_4308_: *mut LeanObject,
    mut v_x_4309_: *mut LeanObject,
    mut v_x_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5877__boxed_4311_: usize = 0;
    let mut v_res_4312_: u8 = 0;
    let mut v_r_4313_: *mut LeanObject = core::ptr::null_mut();
    v_x_5877__boxed_4311_ = lean_unbox_usize(v_x_4309_);
    lean_dec(v_x_4309_);
    v_res_4312_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_4307_, v_x_4308_, v_x_5877__boxed_4311_, v_x_4310_);
    lean_dec_ref(v_x_4310_);
    lean_dec_ref(v_x_4308_);
    v_r_4313_ = lean_box((v_res_4312_) as usize);
    return v_r_4313_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12(
    mut v_00_u03b2_4314_: *mut LeanObject,
    mut v_keys_4315_: *mut LeanObject,
    mut v_vals_4316_: *mut LeanObject,
    mut v_heq_4317_: *mut LeanObject,
    mut v_i_4318_: *mut LeanObject,
    mut v_k_4319_: *mut LeanObject,
) -> u8 {
    let mut v___x_4320_: u8 = 0;
    v___x_4320_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___redArg(v_keys_4315_, v_i_4318_, v_k_4319_);
    return v___x_4320_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12___boxed(
    mut v_00_u03b2_4321_: *mut LeanObject,
    mut v_keys_4322_: *mut LeanObject,
    mut v_vals_4323_: *mut LeanObject,
    mut v_heq_4324_: *mut LeanObject,
    mut v_i_4325_: *mut LeanObject,
    mut v_k_4326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4327_: u8 = 0;
    let mut v_r_4328_: *mut LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Compiler_CSimp_replaceConstant_x3f_spec__1_spec__3_spec__6_spec__10_spec__12(v_00_u03b2_4321_, v_keys_4322_, v_vals_4323_, v_heq_4324_, v_i_4325_, v_k_4326_);
    lean_dec_ref(v_k_4326_);
    lean_dec_ref(v_vals_4323_);
    lean_dec_ref(v_keys_4322_);
    v_r_4328_ = lean_box((v_res_4327_) as usize);
    return v_r_4328_;
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant(
    mut v_env_4329_: *mut LeanObject,
    mut v_e_4330_: *mut LeanObject,
    mut v_a_4331_: *mut LeanObject,
    mut v_a_4332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_a_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4334_ = l_Lean_Compiler_CSimp_replaceConstant_x3f(
                    v_env_4329_,
                    v_e_4330_,
                    v_a_4331_,
                    v_a_4332_,
                );
                if lean_obj_tag(v___x_4334_) == 0 {
                    v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4346_ = (!lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4337_ = v___x_4334_;
                        v_isShared_4338_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4335_);
                        lean_dec(v___x_4334_);
                        v___x_4337_ = lean_box(0);
                        v_isShared_4338_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4330_);
                    v_a_4347_ = lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4354_ = (!lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4349_ = v___x_4334_;
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4347_);
                        lean_dec(v___x_4334_);
                        v___x_4349_ = lean_box(0);
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4335_) == 0 {
                    if v_isShared_4338_ == 0 {
                        lean_ctor_set(v___x_4337_, 0, v_e_4330_);
                        v___x_4340_ = v___x_4337_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_e_4330_);
                        v___x_4340_ = v_reuseFailAlloc_4341_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4330_);
                    v_val_4342_ = lean_ctor_get(v_a_4335_, 0);
                    lean_inc(v_val_4342_);
                    lean_dec_ref_known(v_a_4335_, 1);
                    if v_isShared_4338_ == 0 {
                        lean_ctor_set(v___x_4337_, 0, v_val_4342_);
                        v___x_4344_ = v___x_4337_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_val_4342_);
                        v___x_4344_ = v_reuseFailAlloc_4345_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4340_;
            }
            3 => {
                return v___x_4344_;
            }
            4 => {
                if v_isShared_4350_ == 0 {
                    v___x_4352_ = v___x_4349_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_CSimp_replaceConstant___boxed(
    mut v_env_4355_: *mut LeanObject,
    mut v_e_4356_: *mut LeanObject,
    mut v_a_4357_: *mut LeanObject,
    mut v_a_4358_: *mut LeanObject,
    mut v_a_4359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4360_: *mut LeanObject = core::ptr::null_mut();
    v_res_4360_ =
        l_Lean_Compiler_CSimp_replaceConstant(v_env_4355_, v_e_4356_, v_a_4357_, v_a_4358_);
    lean_dec(v_a_4358_);
    lean_dec_ref(v_a_4357_);
    return v_res_4360_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_keys_4361_: *mut LeanObject,
    mut v_i_4362_: *mut LeanObject,
    mut v_k_4363_: *mut LeanObject,
) -> u8 {
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: u8 = 0;
    let mut v_k_x27_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4364_ = lean_array_get_size(v_keys_4361_);
                v___x_4365_ = lean_nat_dec_lt(v_i_4362_, v___x_4364_);
                if v___x_4365_ == 0 {
                    lean_dec(v_i_4362_);
                    return v___x_4365_;
                } else {
                    v_k_x27_4366_ = lean_array_fget_borrowed(v_keys_4361_, v_i_4362_);
                    v___x_4367_ = lean_name_eq(v_k_4363_, v_k_x27_4366_);
                    if v___x_4367_ == 0 {
                        v___x_4368_ = lean_unsigned_to_nat(1);
                        v___x_4369_ = lean_nat_add(v_i_4362_, v___x_4368_);
                        lean_dec(v_i_4362_);
                        v_i_4362_ = v___x_4369_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4362_);
                        return v___x_4367_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_4371_: *mut LeanObject,
    mut v_i_4372_: *mut LeanObject,
    mut v_k_4373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4374_: u8 = 0;
    let mut v_r_4375_: *mut LeanObject = core::ptr::null_mut();
    v_res_4374_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_4371_, v_i_4372_, v_k_4373_);
    lean_dec(v_k_4373_);
    lean_dec_ref(v_keys_4371_);
    v_r_4375_ = lean_box((v_res_4374_) as usize);
    return v_r_4375_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(
    mut v_x_4376_: *mut LeanObject,
    mut v_x_4377_: usize,
    mut v_x_4378_: *mut LeanObject,
) -> u8 {
    let mut v_es_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: usize = 0;
    let mut v___x_4382_: usize = 0;
    let mut v___x_4383_: usize = 0;
    let mut v_j_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    let mut v_node_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: usize = 0;
    let mut v___x_4391_: u8 = 0;
    let mut v_ks_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4376_) == 0 {
                    v_es_4379_ = lean_ctor_get(v_x_4376_, 0);
                    v___x_4380_ = lean_box(2);
                    v___x_4381_ = 5usize;
                    v___x_4382_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4383_ = lean_usize_land(v_x_4377_, v___x_4382_);
                    v_j_4384_ = lean_usize_to_nat(v___x_4383_);
                    v___x_4385_ = lean_array_get_borrowed(v___x_4380_, v_es_4379_, v_j_4384_);
                    lean_dec(v_j_4384_);
                    match lean_obj_tag(v___x_4385_) {
                        0 => {
                            v_key_4386_ = lean_ctor_get(v___x_4385_, 0);
                            v___x_4387_ = lean_name_eq(v_x_4378_, v_key_4386_);
                            return v___x_4387_;
                        }
                        1 => {
                            v_node_4388_ = lean_ctor_get(v___x_4385_, 0);
                            v___x_4389_ = lean_usize_shift_right(v_x_4377_, v___x_4381_);
                            v_x_4376_ = v_node_4388_;
                            v_x_4377_ = v___x_4389_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4391_ = 0;
                            return v___x_4391_;
                        }
                    }
                } else {
                    v_ks_4392_ = lean_ctor_get(v_x_4376_, 0);
                    v___x_4393_ = lean_unsigned_to_nat(0);
                    v___x_4394_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_4392_, v___x_4393_, v_x_4378_);
                    return v___x_4394_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_4395_: *mut LeanObject,
    mut v_x_4396_: *mut LeanObject,
    mut v_x_4397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_228__boxed_4398_: usize = 0;
    let mut v_res_4399_: u8 = 0;
    let mut v_r_4400_: *mut LeanObject = core::ptr::null_mut();
    v_x_228__boxed_4398_ = lean_unbox_usize(v_x_4396_);
    lean_dec(v_x_4396_);
    v_res_4399_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(v_x_4395_, v_x_228__boxed_4398_, v_x_4397_);
    lean_dec(v_x_4397_);
    lean_dec_ref(v_x_4395_);
    v_r_4400_ = lean_box((v_res_4399_) as usize);
    return v_r_4400_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(
    mut v_x_4401_: *mut LeanObject,
    mut v_x_4402_: *mut LeanObject,
) -> u8 {
    let mut v___y_4404_: u64 = 0;
    let mut v___x_4405_: usize = 0;
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: u64 = 0;
    let mut v_hash_4408_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4402_) == 0 {
                    v___x_4407_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_4404_ = v___x_4407_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4408_ = lean_ctor_get_uint64(
                        v_x_4402_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4404_ = v_hash_4408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4405_ = lean_uint64_to_usize(v___y_4404_);
                v___x_4406_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(v_x_4401_, v___x_4405_, v_x_4402_);
                return v___x_4406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg___boxed(
    mut v_x_4409_: *mut LeanObject,
    mut v_x_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4411_: u8 = 0;
    let mut v_r_4412_: *mut LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(v_x_4409_, v_x_4410_);
    lean_dec(v_x_4410_);
    lean_dec_ref(v_x_4409_);
    v_r_4412_ = lean_box((v_res_4411_) as usize);
    return v_r_4412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(
    mut v_m_4413_: *mut LeanObject,
    mut v_a_4414_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: u64 = 0;
    let mut v___x_4419_: u64 = 0;
    let mut v___x_4420_: u64 = 0;
    let mut v_fold_4421_: u64 = 0;
    let mut v___x_4422_: u64 = 0;
    let mut v___x_4423_: u64 = 0;
    let mut v___x_4424_: u64 = 0;
    let mut v___x_4425_: usize = 0;
    let mut v___x_4426_: usize = 0;
    let mut v___x_4427_: usize = 0;
    let mut v___x_4428_: usize = 0;
    let mut v___x_4429_: usize = 0;
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: u8 = 0;
    let mut v___x_4432_: u64 = 0;
    let mut v_hash_4433_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4415_ = lean_ctor_get(v_m_4413_, 1);
                v___x_4416_ = lean_array_get_size(v_buckets_4415_);
                if lean_obj_tag(v_a_4414_) == 0 {
                    v___x_4432_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_4418_ = v___x_4432_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4433_ = lean_ctor_get_uint64(
                        v_a_4414_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4418_ = v_hash_4433_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4419_ = 32u64;
                v___x_4420_ = lean_uint64_shift_right(v___y_4418_, v___x_4419_);
                v_fold_4421_ = lean_uint64_xor(v___y_4418_, v___x_4420_);
                v___x_4422_ = 16u64;
                v___x_4423_ = lean_uint64_shift_right(v_fold_4421_, v___x_4422_);
                v___x_4424_ = lean_uint64_xor(v_fold_4421_, v___x_4423_);
                v___x_4425_ = lean_uint64_to_usize(v___x_4424_);
                v___x_4426_ = lean_usize_of_nat(v___x_4416_);
                v___x_4427_ = 1usize;
                v___x_4428_ = lean_usize_sub(v___x_4426_, v___x_4427_);
                v___x_4429_ = lean_usize_land(v___x_4425_, v___x_4428_);
                v___x_4430_ = lean_array_uget_borrowed(v_buckets_4415_, v___x_4429_);
                v___x_4431_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_a_4414_, v___x_4430_);
                return v___x_4431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg___boxed(
    mut v_m_4434_: *mut LeanObject,
    mut v_a_4435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4436_: u8 = 0;
    let mut v_r_4437_: *mut LeanObject = core::ptr::null_mut();
    v_res_4436_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_m_4434_, v_a_4435_);
    lean_dec(v_a_4435_);
    lean_dec_ref(v_m_4434_);
    v_r_4437_ = lean_box((v_res_4436_) as usize);
    return v_r_4437_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
    mut v_x_4438_: *mut LeanObject,
    mut v_x_4439_: *mut LeanObject,
) -> u8 {
    let mut v_stage_u2081_4440_: u8 = 0;
    v_stage_u2081_4440_ = lean_ctor_get_uint8(
        v_x_4438_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_4440_ == 0 {
        let mut v_map_u2081_4441_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_4442_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4443_: u8 = 0;
        v_map_u2081_4441_ = lean_ctor_get(v_x_4438_, 0);
        v_map_u2082_4442_ = lean_ctor_get(v_x_4438_, 1);
        v___x_4443_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_map_u2081_4441_, v_x_4439_);
        if v___x_4443_ == 0 {
            let mut v___x_4444_: u8 = 0;
            v___x_4444_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(v_map_u2082_4442_, v_x_4439_);
            return v___x_4444_;
        } else {
            return v___x_4443_;
        }
    } else {
        let mut v_map_u2081_4445_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4446_: u8 = 0;
        v_map_u2081_4445_ = lean_ctor_get(v_x_4438_, 0);
        v___x_4446_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_map_u2081_4445_, v_x_4439_);
        return v___x_4446_;
    }
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg___boxed(
    mut v_x_4447_: *mut LeanObject,
    mut v_x_4448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4449_: u8 = 0;
    let mut v_r_4450_: *mut LeanObject = core::ptr::null_mut();
    v_res_4449_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
        v_x_4447_, v_x_4448_,
    );
    lean_dec(v_x_4448_);
    lean_dec_ref(v_x_4447_);
    v_r_4450_ = lean_box((v_res_4449_) as usize);
    return v_r_4450_;
}
pub unsafe fn l_Lean_Compiler_hasCSimpAttribute(
    mut v_env_4451_: *mut LeanObject,
    mut v_declName_4452_: *mut LeanObject,
) -> u8 {
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_thmNames_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    v___x_4453_ = l_Lean_Compiler_CSimp_ext;
    v_ext_4454_ = lean_ctor_get(v___x_4453_, 1);
    v_toEnvExtension_4455_ = lean_ctor_get(v_ext_4454_, 0);
    v_asyncMode_4456_ = lean_ctor_get(v_toEnvExtension_4455_, 2);
    v___x_4457_ = l_Lean_Compiler_CSimp_instInhabitedState_default;
    v___x_4458_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_4457_,
        v___x_4453_,
        v_env_4451_,
        v_asyncMode_4456_,
    );
    v_thmNames_4459_ = lean_ctor_get(v___x_4458_, 1);
    lean_inc_ref(v_thmNames_4459_);
    lean_dec(v___x_4458_);
    v___x_4460_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
        v_thmNames_4459_,
        v_declName_4452_,
    );
    lean_dec_ref(v_thmNames_4459_);
    return v___x_4460_;
}
pub unsafe fn l_Lean_Compiler_hasCSimpAttribute___boxed(
    mut v_env_4461_: *mut LeanObject,
    mut v_declName_4462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4463_: u8 = 0;
    let mut v_r_4464_: *mut LeanObject = core::ptr::null_mut();
    v_res_4463_ = l_Lean_Compiler_hasCSimpAttribute(v_env_4461_, v_declName_4462_);
    lean_dec(v_declName_4462_);
    v_r_4464_ = lean_box((v_res_4463_) as usize);
    return v_r_4464_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0(
    mut v_00_u03b2_4465_: *mut LeanObject,
    mut v_x_4466_: *mut LeanObject,
    mut v_x_4467_: *mut LeanObject,
) -> u8 {
    let mut v___x_4468_: u8 = 0;
    v___x_4468_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___redArg(
        v_x_4466_, v_x_4467_,
    );
    return v___x_4468_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0___boxed(
    mut v_00_u03b2_4469_: *mut LeanObject,
    mut v_x_4470_: *mut LeanObject,
    mut v_x_4471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4472_: u8 = 0;
    let mut v_r_4473_: *mut LeanObject = core::ptr::null_mut();
    v_res_4472_ = l_Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0(
        v_00_u03b2_4469_,
        v_x_4470_,
        v_x_4471_,
    );
    lean_dec(v_x_4471_);
    lean_dec_ref(v_x_4470_);
    v_r_4473_ = lean_box((v_res_4472_) as usize);
    return v_r_4473_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0(
    mut v_00_u03b2_4474_: *mut LeanObject,
    mut v_m_4475_: *mut LeanObject,
    mut v_a_4476_: *mut LeanObject,
) -> u8 {
    let mut v___x_4477_: u8 = 0;
    v___x_4477_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___redArg(v_m_4475_, v_a_4476_);
    return v___x_4477_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0___boxed(
    mut v_00_u03b2_4478_: *mut LeanObject,
    mut v_m_4479_: *mut LeanObject,
    mut v_a_4480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4481_: u8 = 0;
    let mut v_r_4482_: *mut LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__0(v_00_u03b2_4478_, v_m_4479_, v_a_4480_);
    lean_dec(v_a_4480_);
    lean_dec_ref(v_m_4479_);
    v_r_4482_ = lean_box((v_res_4481_) as usize);
    return v_r_4482_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1(
    mut v_00_u03b2_4483_: *mut LeanObject,
    mut v_x_4484_: *mut LeanObject,
    mut v_x_4485_: *mut LeanObject,
) -> u8 {
    let mut v___x_4486_: u8 = 0;
    v___x_4486_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___redArg(v_x_4484_, v_x_4485_);
    return v___x_4486_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1___boxed(
    mut v_00_u03b2_4487_: *mut LeanObject,
    mut v_x_4488_: *mut LeanObject,
    mut v_x_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1(v_00_u03b2_4487_, v_x_4488_, v_x_4489_);
    lean_dec(v_x_4489_);
    lean_dec_ref(v_x_4488_);
    v_r_4491_ = lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4492_: *mut LeanObject,
    mut v_x_4493_: *mut LeanObject,
    mut v_x_4494_: usize,
    mut v_x_4495_: *mut LeanObject,
) -> u8 {
    let mut v___x_4496_: u8 = 0;
    v___x_4496_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___redArg(v_x_4493_, v_x_4494_, v_x_4495_);
    return v___x_4496_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4497_: *mut LeanObject,
    mut v_x_4498_: *mut LeanObject,
    mut v_x_4499_: *mut LeanObject,
    mut v_x_4500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_374__boxed_4501_: usize = 0;
    let mut v_res_4502_: u8 = 0;
    let mut v_r_4503_: *mut LeanObject = core::ptr::null_mut();
    v_x_374__boxed_4501_ = lean_unbox_usize(v_x_4499_);
    lean_dec(v_x_4499_);
    v_res_4502_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2(v_00_u03b2_4497_, v_x_4498_, v_x_374__boxed_4501_, v_x_4500_);
    lean_dec(v_x_4500_);
    lean_dec_ref(v_x_4498_);
    v_r_4503_ = lean_box((v_res_4502_) as usize);
    return v_r_4503_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4504_: *mut LeanObject,
    mut v_keys_4505_: *mut LeanObject,
    mut v_vals_4506_: *mut LeanObject,
    mut v_heq_4507_: *mut LeanObject,
    mut v_i_4508_: *mut LeanObject,
    mut v_k_4509_: *mut LeanObject,
) -> u8 {
    let mut v___x_4510_: u8 = 0;
    v___x_4510_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_4505_, v_i_4508_, v_k_4509_);
    return v___x_4510_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_4511_: *mut LeanObject,
    mut v_keys_4512_: *mut LeanObject,
    mut v_vals_4513_: *mut LeanObject,
    mut v_heq_4514_: *mut LeanObject,
    mut v_i_4515_: *mut LeanObject,
    mut v_k_4516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4517_: u8 = 0;
    let mut v_r_4518_: *mut LeanObject = core::ptr::null_mut();
    v_res_4517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_Compiler_hasCSimpAttribute_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_4511_, v_keys_4512_, v_vals_4513_, v_heq_4514_, v_i_4515_, v_k_4516_);
    lean_dec(v_k_4516_);
    lean_dec_ref(v_vals_4513_);
    lean_dec_ref(v_keys_4512_);
    v_r_4518_ = lean_box((v_res_4517_) as usize);
    return v_r_4518_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_CSimpAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_CSimp_instInhabitedState_default =
        _init_l_Lean_Compiler_CSimp_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedState_default);
    l_Lean_Compiler_CSimp_instInhabitedState = _init_l_Lean_Compiler_CSimp_instInhabitedState();
    lean_mark_persistent(l_Lean_Compiler_CSimp_instInhabitedState);
    res = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_00___x40_Lean_Compiler_CSimpAttr_309491121____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_CSimp_ext = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_CSimp_ext);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn___regBuiltin___private_Lean_Compiler_CSimpAttr_0__Lean_Compiler_CSimp_initFn_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_CSimpAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_CSimpAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ExtraModUses(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_CSimpAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_CSimpAttr(builtin);
}
