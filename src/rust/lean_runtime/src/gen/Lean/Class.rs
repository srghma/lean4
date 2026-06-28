// Lean compiler output
// Module: Lean.Class
// Imports: Lean.Attributes Lean.Util.CollectLevelParams
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_Attribute_Builtin_ensureNoArgs,
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
    runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isInstImplicit, l_Lean_Expr_appArg_x21, l_Lean_Expr_bindingBody_x21,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_forallE___override, l_Lean_Expr_hasFVar,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr,
    l_Lean_mkFVar, lean_is_out_param,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::CollectLevelParams::{
    initialize_Lean_Util_CollectLevelParams, l_Lean_collectLevelParams,
    runtime_initialize_Lean_Util_CollectLevelParams,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
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
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_panic_fn_borrowed, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instInhabitedClassState_default___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedClassState_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedClassState_default___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instInhabitedClassState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedClassState_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedClassState: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Class_0__Lean_initFn___lam__0_00___x40_Lean_Class_903839608____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_903839608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_903839608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [99, 108, 97, 115, 115, 69, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_903839608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,10430853664991602840 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_903839608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_ClassState_addEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_903839608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_903839608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_checkOutParam___closed__0_value: LeanStringObject<6> =
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
        m_data: [95, 102, 118, 97, 114, 0],
    };
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_checkOutParam___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_checkOutParam___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_checkOutParam___closed__0_value)
                as *mut LeanObject,
            6732666334398091176 as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_checkOutParam___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_checkOutParam___closed__2_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 99, 108, 97, 115, 115, 44, 32, 112, 97, 114, 97,
            109, 101, 116, 101, 114, 32, 35, 0,
        ],
    };
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_checkOutParam___closed__2_value)
        as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_checkOutParam___closed__4_value: LeanStringObject<52> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            32, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 96, 111, 117, 116, 80, 97,
            114, 97, 109, 96, 44, 32, 98, 117, 116, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116,
            32, 97, 110, 32, 96, 111, 117, 116, 80, 97, 114, 97, 109, 96, 0,
        ],
    };
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_checkOutParam___closed__4_value)
        as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_checkOutParam___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__0_value:
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
    m_data: [76, 101, 97, 110, 46, 69, 120, 112, 114, 0],
};
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__1_value:
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
        76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 70, 111, 114, 97,
        108, 108, 69, 33, 0,
    ],
};
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__2_value:
    LeanStringObject<16> = LeanStringObject {
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
        102, 111, 114, 97, 108, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__2_value)
        as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__4_value:
    LeanStringObject<49> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 48,
        46, 76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 70, 111, 114,
        97, 108, 108, 33, 73, 109, 112, 108, 0,
    ],
};
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__4_value)
        as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkOutParamArgsImplicit___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_mkOutParamArgsImplicit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkOutParamArgsImplicit___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_mkOutParamArgsImplicit___closed__0_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_addClass___closed__0_value: LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 39, 99, 108, 97, 115, 115, 39, 44, 32, 100, 101, 99,
        108, 97, 114, 97, 116, 105, 111, 110, 32, 39, 0,
    ],
};
static mut l_Lean_addClass___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addClass___closed__0_value) as *mut LeanObject;
static mut l_Lean_addClass___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addClass___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_addClass___closed__2_value: LeanStringObject<53> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        39, 32, 109, 117, 115, 116, 32, 98, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101,
        32, 100, 97, 116, 97, 116, 121, 112, 101, 44, 32, 115, 116, 114, 117, 99, 116, 117, 114,
        101, 44, 32, 111, 114, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0,
    ],
};
static mut l_Lean_addClass___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addClass___closed__2_value) as *mut LeanObject;
static mut l_Lean_addClass___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addClass___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_addClass___closed__4_value: LeanStringObject<22> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 39, 0,
    ],
};
static mut l_Lean_addClass___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addClass___closed__4_value) as *mut LeanObject;
static mut l_Lean_addClass___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addClass___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_addClass___closed__6_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l_Lean_addClass___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addClass___closed__6_value) as *mut LeanObject;
static mut l_Lean_addClass___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addClass___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_addClass___closed__8_value: LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        99, 108, 97, 115, 115, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101,
        101, 110, 32, 100, 101, 99, 108, 97, 114, 101, 100, 32, 39, 0,
    ],
};
static mut l_Lean_addClass___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_addClass___closed__8_value) as *mut LeanObject;
static mut l_Lean_addClass___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addClass___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__2_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___lam__1___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l___private_Lean_Class_0__Lean_init___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___lam__1___closed__0_value)
        as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_init___lam__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_init___lam__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_init___lam__1___closed__2_value: LeanStringObject<20> =
    LeanStringObject {
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
            93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___lam__1___closed__2_value)
        as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_init___lam__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Class_0__Lean_init___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_init___closed__0_value: LeanStringObject<9> =
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
        m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__0_value)
                as *mut LeanObject,
            11079354408986465895 as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_init___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__3_value: LeanStringObject<6> =
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
        m_data: [67, 108, 97, 115, 115, 0],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__3_value)
                as *mut LeanObject,
            7259278760647018593 as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            9273346084189984516 as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,453937697259300325 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_init___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__7_value: LeanStringObject<5> =
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
        m_data: [105, 110, 105, 116, 0],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__7_value)
                as *mut LeanObject,
            13544375753058581422 as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__9_value: LeanStringObject<6> =
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
        m_data: [99, 108, 97, 115, 115, 0],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__9_value)
                as *mut LeanObject,
            4225540988494793473 as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__11_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Class_0__Lean_init___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__12_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l___private_Lean_Class_0__Lean_init___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__13_value: LeanStringObject<11> =
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
        m_data: [116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 0],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__14_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__13_value)
                as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__11_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l___private_Lean_Class_0__Lean_init___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1___closed__0_value: LeanStringObject<183> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 183, m_capacity: 183, m_length: 182, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 111, 114, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 97, 115, 32, 97, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 46, 32, 85, 115, 105, 110, 103, 32, 96, 99, 108, 97, 115, 115, 96, 32, 111, 114, 32, 96, 99, 108, 97, 115, 115, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 96, 32, 105, 115, 10, 103, 101, 110, 101, 114, 97, 108, 108, 121, 32, 112, 114, 101, 102, 101, 114, 114, 101, 100, 32, 111, 118, 101, 114, 32, 117, 115, 105, 110, 103, 32, 96, 64, 91, 99, 108, 97, 115, 115, 93, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 96, 32, 111, 114, 32, 96, 64, 91, 99, 108, 97, 115, 115, 93, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 96, 32, 100, 105, 114, 101, 99, 116, 108, 121, 46, 10, 0]};
static mut l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__0_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 111, 102, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 117, 110, 105, 118, 95, 111, 117, 116, 95, 112, 97, 114, 97, 109, 115, 96, 44, 32, 96, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Class_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 108, 97, 115, 115, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Class_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Class_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,11044912918815677548 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,16982064854406403013 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__2_00___x40_Lean_Class_903839608____hygCtx___hyg_2__value) as *mut LeanObject,886934183020025872 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__4_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_init___closed__3_value) as *mut LeanObject,11779813151579338275 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__5_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,((( 1274053790 as usize) << 1) | 1) as *mut LeanObject,9531219347153322227 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__7_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__7_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__7_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__8_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__7_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,10994721237591734248 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__8_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__8_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__9_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__9_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__9_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__10_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__8_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__9_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,1189186386000836460 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__10_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__10_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__11_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__10_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,1099541633400697301 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__11_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__11_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__12_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [117, 110, 105, 118, 95, 111, 117, 116, 95, 112, 97, 114, 97, 109, 115, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__12_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__12_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__13_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__12_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,206318846432384360 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__13_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__13_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__14_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Class_0__Lean_initFn___lam__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__13_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__14_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__14_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__15_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__13_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__15_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__15_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__16_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanStringObject<44> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [117, 110, 105, 118, 101, 114, 115, 101, 32, 111, 117, 116, 112, 117, 116, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 102, 111, 114, 32, 97, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 0]};
static mut l___private_Lean_Class_0__Lean_initFn___closed__16_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__16_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__17_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__11_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__13_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__16_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__17_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__17_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Class_0__Lean_initFn___closed__18_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__17_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__14_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__15_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Class_0__Lean_initFn___closed__18_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Class_0__Lean_initFn___closed__18_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_ClassEntry_lt(
    mut v_a_2241_: *mut LeanObject,
    mut v_b_2242_: *mut LeanObject,
) -> u8 {
    let mut v_name_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: u8 = 0;
    v_name_2243_ = lean_ctor_get(v_a_2241_, 0);
    v_name_2244_ = lean_ctor_get(v_b_2242_, 0);
    v___x_2245_ = l_Lean_Name_quickLt(v_name_2243_, v_name_2244_);
    return v___x_2245_;
}
pub unsafe fn l_Lean_ClassEntry_lt___boxed(
    mut v_a_2246_: *mut LeanObject,
    mut v_b_2247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2248_: u8 = 0;
    let mut v_r_2249_: *mut LeanObject = core::ptr::null_mut();
    v_res_2248_ = l_Lean_ClassEntry_lt(v_a_2246_, v_b_2247_);
    lean_dec_ref(v_b_2247_);
    lean_dec_ref(v_a_2246_);
    v_r_2249_ = lean_box((v_res_2248_) as usize);
    return v_r_2249_;
}
pub unsafe fn _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ = lean_box(0);
    v___x_2251_ = lean_unsigned_to_nat(16);
    v___x_2252_ = lean_mk_array(v___x_2251_, v___x_2250_);
    return v___x_2252_;
}
pub unsafe fn _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    v___x_2253_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__0_once), _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__0);
    v___x_2254_ = lean_unsigned_to_nat(0);
    v___x_2255_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2255_, 0, v___x_2254_);
    lean_ctor_set(v___x_2255_, 1, v___x_2253_);
    return v___x_2255_;
}
pub unsafe fn _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    v___x_2256_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2256_;
}
pub unsafe fn _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    v___x_2257_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__2_once), _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__2);
    v___x_2258_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2258_, 0, v___x_2257_);
    return v___x_2258_;
}
pub unsafe fn _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    v___x_2259_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__3_once), _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__3);
    v___x_2260_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__1_once), _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__1);
    v___x_2261_ = 1;
    v___x_2262_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_2262_, 0, v___x_2260_);
    lean_ctor_set(v___x_2262_, 1, v___x_2259_);
    lean_ctor_set_uint8(
        v___x_2262_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_2261_,
    );
    return v___x_2262_;
}
pub unsafe fn l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0(
    mut v_00_u03b2_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    v___x_2264_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__4_once), _init_l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0___closed__4);
    return v___x_2264_;
}
pub unsafe fn _init_l_Lean_instInhabitedClassState_default___closed__0() -> *mut LeanObject {
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    v___x_2265_ =
        l_Lean_SMap_empty___at___00Lean_instInhabitedClassState_default_spec__0(lean_box(0));
    return v___x_2265_;
}
pub unsafe fn _init_l_Lean_instInhabitedClassState_default___closed__1() -> *mut LeanObject {
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    v___x_2266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClassState_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClassState_default___closed__0_once),
        _init_l_Lean_instInhabitedClassState_default___closed__0,
    );
    v___x_2267_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2267_, 0, v___x_2266_);
    lean_ctor_set(v___x_2267_, 1, v___x_2266_);
    return v___x_2267_;
}
pub unsafe fn _init_l_Lean_instInhabitedClassState_default() -> *mut LeanObject {
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    v___x_2268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClassState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClassState_default___closed__1_once),
        _init_l_Lean_instInhabitedClassState_default___closed__1,
    );
    return v___x_2268_;
}
pub unsafe fn _init_l_Lean_instInhabitedClassState() -> *mut LeanObject {
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    v___x_2269_ = l_Lean_instInhabitedClassState_default;
    return v___x_2269_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_x_2270_: *mut LeanObject,
    mut v_x_2271_: *mut LeanObject,
    mut v_x_2272_: *mut LeanObject,
    mut v_x_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2278_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2274_ = lean_ctor_get(v_x_2270_, 0);
                v_vs_2275_ = lean_ctor_get(v_x_2270_, 1);
                v_isSharedCheck_2299_ = (!lean_is_exclusive(v_x_2270_)) as u8;
                if v_isSharedCheck_2299_ == 0 {
                    v___x_2277_ = v_x_2270_;
                    v_isShared_2278_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2275_);
                    lean_inc(v_ks_2274_);
                    lean_dec(v_x_2270_);
                    v___x_2277_ = lean_box(0);
                    v_isShared_2278_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2279_ = lean_array_get_size(v_ks_2274_);
                v___x_2280_ = lean_nat_dec_lt(v_x_2271_, v___x_2279_);
                if v___x_2280_ == 0 {
                    lean_dec(v_x_2271_);
                    v___x_2281_ = lean_array_push(v_ks_2274_, v_x_2272_);
                    v___x_2282_ = lean_array_push(v_vs_2275_, v_x_2273_);
                    if v_isShared_2278_ == 0 {
                        lean_ctor_set(v___x_2277_, 1, v___x_2282_);
                        lean_ctor_set(v___x_2277_, 0, v___x_2281_);
                        v___x_2284_ = v___x_2277_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2281_);
                        lean_ctor_set(v_reuseFailAlloc_2285_, 1, v___x_2282_);
                        v___x_2284_ = v_reuseFailAlloc_2285_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2286_ = lean_array_fget_borrowed(v_ks_2274_, v_x_2271_);
                    v___x_2287_ = lean_name_eq(v_x_2272_, v_k_x27_2286_);
                    if v___x_2287_ == 0 {
                        if v_isShared_2278_ == 0 {
                            v___x_2289_ = v___x_2277_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_ks_2274_);
                            lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_vs_2275_);
                            v___x_2289_ = v_reuseFailAlloc_2293_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2294_ = lean_array_fset(v_ks_2274_, v_x_2271_, v_x_2272_);
                        v___x_2295_ = lean_array_fset(v_vs_2275_, v_x_2271_, v_x_2273_);
                        lean_dec(v_x_2271_);
                        if v_isShared_2278_ == 0 {
                            lean_ctor_set(v___x_2277_, 1, v___x_2295_);
                            lean_ctor_set(v___x_2277_, 0, v___x_2294_);
                            v___x_2297_ = v___x_2277_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2294_);
                            lean_ctor_set(v_reuseFailAlloc_2298_, 1, v___x_2295_);
                            v___x_2297_ = v_reuseFailAlloc_2298_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2284_;
            }
            3 => {
                v___x_2290_ = lean_unsigned_to_nat(1);
                v___x_2291_ = lean_nat_add(v_x_2271_, v___x_2290_);
                lean_dec(v_x_2271_);
                v_x_2270_ = v___x_2289_;
                v_x_2271_ = v___x_2291_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_n_2300_: *mut LeanObject,
    mut v_k_2301_: *mut LeanObject,
    mut v_v_2302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v___x_2303_ = lean_unsigned_to_nat(0);
    v___x_2304_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_n_2300_, v___x_2303_, v_k_2301_, v_v_2302_);
    return v___x_2304_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: u64 = 0;
    v___x_2305_ = lean_unsigned_to_nat(1723);
    v___x_2306_ = lean_uint64_of_nat(v___x_2305_);
    return v___x_2306_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: usize = 0;
    let mut v___x_2309_: usize = 0;
    v___x_2307_ = 5usize;
    v___x_2308_ = 1usize;
    v___x_2309_ = lean_usize_shift_left(v___x_2308_, v___x_2307_);
    return v___x_2309_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2310_: usize = 0;
    let mut v___x_2311_: usize = 0;
    let mut v___x_2312_: usize = 0;
    v___x_2310_ = 1usize;
    v___x_2311_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2312_ = lean_usize_sub(v___x_2311_, v___x_2310_);
    return v___x_2312_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    v___x_2313_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2313_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg(
    mut v_x_2314_: *mut LeanObject,
    mut v_x_2315_: usize,
    mut v_x_2316_: usize,
    mut v_x_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: usize = 0;
    let mut v___x_2322_: usize = 0;
    let mut v___x_2323_: usize = 0;
    let mut v_j_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v_v_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2343_: u8 = 0;
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2350_: u8 = 0;
    let mut v_node_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2354_: u8 = 0;
    let mut v___x_2355_: usize = 0;
    let mut v___x_2356_: usize = 0;
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_unused_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2374_: u8 = 0;
    let mut v_ks_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: usize = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: u8 = 0;
    let mut v_reuseFailAlloc_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2314_) == 0 {
                    v_es_2319_ = lean_ctor_get(v_x_2314_, 0);
                    v___x_2320_ = 5usize;
                    v___x_2321_ = 1usize;
                    v___x_2322_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2323_ = lean_usize_land(v_x_2315_, v___x_2322_);
                    v_j_2324_ = lean_usize_to_nat(v___x_2323_);
                    v___x_2325_ = lean_array_get_size(v_es_2319_);
                    v___x_2326_ = lean_nat_dec_lt(v_j_2324_, v___x_2325_);
                    if v___x_2326_ == 0 {
                        lean_dec(v_j_2324_);
                        lean_dec(v_x_2318_);
                        lean_dec(v_x_2317_);
                        return v_x_2314_;
                    } else {
                        lean_inc_ref(v_es_2319_);
                        v_isSharedCheck_2363_ = (!lean_is_exclusive(v_x_2314_)) as u8;
                        if v_isSharedCheck_2363_ == 0 {
                            v_unused_2364_ = lean_ctor_get(v_x_2314_, 0);
                            lean_dec(v_unused_2364_);
                            v___x_2328_ = v_x_2314_;
                            v_isShared_2329_ = v_isSharedCheck_2363_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2314_);
                            v___x_2328_ = lean_box(0);
                            v_isShared_2329_ = v_isSharedCheck_2363_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2365_ = lean_ctor_get(v_x_2314_, 0);
                    v_vs_2366_ = lean_ctor_get(v_x_2314_, 1);
                    v_isSharedCheck_2386_ = (!lean_is_exclusive(v_x_2314_)) as u8;
                    if v_isSharedCheck_2386_ == 0 {
                        v___x_2368_ = v_x_2314_;
                        v_isShared_2369_ = v_isSharedCheck_2386_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2366_);
                        lean_inc(v_ks_2365_);
                        lean_dec(v_x_2314_);
                        v___x_2368_ = lean_box(0);
                        v_isShared_2369_ = v_isSharedCheck_2386_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2330_ = lean_array_fget(v_es_2319_, v_j_2324_);
                v___x_2331_ = lean_box(0);
                v_xs_x27_2332_ = lean_array_fset(v_es_2319_, v_j_2324_, v___x_2331_);
                match lean_obj_tag(v_v_2330_) {
                    0 => {
                        v_key_2339_ = lean_ctor_get(v_v_2330_, 0);
                        v_val_2340_ = lean_ctor_get(v_v_2330_, 1);
                        v_isSharedCheck_2350_ = (!lean_is_exclusive(v_v_2330_)) as u8;
                        if v_isSharedCheck_2350_ == 0 {
                            v___x_2342_ = v_v_2330_;
                            v_isShared_2343_ = v_isSharedCheck_2350_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2340_);
                            lean_inc(v_key_2339_);
                            lean_dec(v_v_2330_);
                            v___x_2342_ = lean_box(0);
                            v_isShared_2343_ = v_isSharedCheck_2350_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2351_ = lean_ctor_get(v_v_2330_, 0);
                        v_isSharedCheck_2361_ = (!lean_is_exclusive(v_v_2330_)) as u8;
                        if v_isSharedCheck_2361_ == 0 {
                            v___x_2353_ = v_v_2330_;
                            v_isShared_2354_ = v_isSharedCheck_2361_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2351_);
                            lean_dec(v_v_2330_);
                            v___x_2353_ = lean_box(0);
                            v_isShared_2354_ = v_isSharedCheck_2361_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2362_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2362_, 0, v_x_2317_);
                        lean_ctor_set(v___x_2362_, 1, v_x_2318_);
                        v___y_2334_ = v___x_2362_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2335_ = lean_array_fset(v_xs_x27_2332_, v_j_2324_, v___y_2334_);
                lean_dec(v_j_2324_);
                if v_isShared_2329_ == 0 {
                    lean_ctor_set(v___x_2328_, 0, v___x_2335_);
                    v___x_2337_ = v___x_2328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
                    v___x_2337_ = v_reuseFailAlloc_2338_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2337_;
            }
            4 => {
                v___x_2344_ = lean_name_eq(v_x_2317_, v_key_2339_);
                if v___x_2344_ == 0 {
                    lean_del_object(v___x_2342_);
                    v___x_2345_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2339_,
                        v_val_2340_,
                        v_x_2317_,
                        v_x_2318_,
                    );
                    v___x_2346_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2346_, 0, v___x_2345_);
                    v___y_2334_ = v___x_2346_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2340_);
                    lean_dec(v_key_2339_);
                    if v_isShared_2343_ == 0 {
                        lean_ctor_set(v___x_2342_, 1, v_x_2318_);
                        lean_ctor_set(v___x_2342_, 0, v_x_2317_);
                        v___x_2348_ = v___x_2342_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_x_2317_);
                        lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_x_2318_);
                        v___x_2348_ = v_reuseFailAlloc_2349_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2334_ = v___x_2348_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2355_ = lean_usize_shift_right(v_x_2315_, v___x_2320_);
                v___x_2356_ = lean_usize_add(v_x_2316_, v___x_2321_);
                v___x_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg(v_node_2351_, v___x_2355_, v___x_2356_, v_x_2317_, v_x_2318_);
                if v_isShared_2354_ == 0 {
                    lean_ctor_set(v___x_2353_, 0, v___x_2357_);
                    v___x_2359_ = v___x_2353_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
                    v___x_2359_ = v_reuseFailAlloc_2360_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2334_ = v___x_2359_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2369_ == 0 {
                    v___x_2371_ = v___x_2368_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_ks_2365_);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_vs_2366_);
                    v___x_2371_ = v_reuseFailAlloc_2385_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2372_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v___x_2371_, v_x_2317_, v_x_2318_);
                v___x_2380_ = 7usize;
                v___x_2381_ = lean_usize_dec_le(v___x_2380_, v_x_2316_);
                if v___x_2381_ == 0 {
                    v___x_2382_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2372_);
                    v___x_2383_ = lean_unsigned_to_nat(4);
                    v___x_2384_ = lean_nat_dec_lt(v___x_2382_, v___x_2383_);
                    lean_dec(v___x_2382_);
                    v___y_2374_ = v___x_2384_;
                    state = 10;
                    continue;
                } else {
                    v___y_2374_ = v___x_2381_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2374_ == 0 {
                    v_ks_2375_ = lean_ctor_get(v_newNode_2372_, 0);
                    lean_inc_ref(v_ks_2375_);
                    v_vs_2376_ = lean_ctor_get(v_newNode_2372_, 1);
                    lean_inc_ref(v_vs_2376_);
                    lean_dec_ref(v_newNode_2372_);
                    v___x_2377_ = lean_unsigned_to_nat(0);
                    v___x_2378_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_2379_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_x_2316_, v_ks_2375_, v_vs_2376_, v___x_2377_, v___x_2378_);
                    lean_dec_ref(v_vs_2376_);
                    lean_dec_ref(v_ks_2375_);
                    return v___x_2379_;
                } else {
                    return v_newNode_2372_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_depth_2387_: usize,
    mut v_keys_2388_: *mut LeanObject,
    mut v_vals_2389_: *mut LeanObject,
    mut v_i_2390_: *mut LeanObject,
    mut v_entries_2391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: u8 = 0;
    let mut v_k_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2397_: u64 = 0;
    let mut v_h_2398_: usize = 0;
    let mut v___x_2399_: usize = 0;
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: usize = 0;
    let mut v___x_2402_: usize = 0;
    let mut v___x_2403_: usize = 0;
    let mut v_h_2404_: usize = 0;
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u64 = 0;
    let mut v_hash_2409_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2392_ = lean_array_get_size(v_keys_2388_);
                v___x_2393_ = lean_nat_dec_lt(v_i_2390_, v___x_2392_);
                if v___x_2393_ == 0 {
                    lean_dec(v_i_2390_);
                    return v_entries_2391_;
                } else {
                    v_k_2394_ = lean_array_fget_borrowed(v_keys_2388_, v_i_2390_);
                    v_v_2395_ = lean_array_fget_borrowed(v_vals_2389_, v_i_2390_);
                    if lean_obj_tag(v_k_2394_) == 0 {
                        v___x_2408_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                        v___y_2397_ = v___x_2408_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2409_ = lean_ctor_get_uint64(
                            v_k_2394_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_2397_ = v_hash_2409_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2398_ = lean_uint64_to_usize(v___y_2397_);
                v___x_2399_ = 5usize;
                v___x_2400_ = lean_unsigned_to_nat(1);
                v___x_2401_ = 1usize;
                v___x_2402_ = lean_usize_sub(v_depth_2387_, v___x_2401_);
                v___x_2403_ = lean_usize_mul(v___x_2399_, v___x_2402_);
                v_h_2404_ = lean_usize_shift_right(v_h_2398_, v___x_2403_);
                v___x_2405_ = lean_nat_add(v_i_2390_, v___x_2400_);
                lean_dec(v_i_2390_);
                lean_inc(v_v_2395_);
                lean_inc(v_k_2394_);
                v___x_2406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg(v_entries_2391_, v_h_2404_, v_depth_2387_, v_k_2394_, v_v_2395_);
                v_i_2390_ = v___x_2405_;
                v_entries_2391_ = v___x_2406_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_depth_2410_: *mut LeanObject,
    mut v_keys_2411_: *mut LeanObject,
    mut v_vals_2412_: *mut LeanObject,
    mut v_i_2413_: *mut LeanObject,
    mut v_entries_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2415_: usize = 0;
    let mut v_res_2416_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2415_ = lean_unbox_usize(v_depth_2410_);
    lean_dec(v_depth_2410_);
    v_res_2416_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_2415_, v_keys_2411_, v_vals_2412_, v_i_2413_, v_entries_2414_);
    lean_dec_ref(v_vals_2412_);
    lean_dec_ref(v_keys_2411_);
    return v_res_2416_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2417_: *mut LeanObject,
    mut v_x_2418_: *mut LeanObject,
    mut v_x_2419_: *mut LeanObject,
    mut v_x_2420_: *mut LeanObject,
    mut v_x_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_806__boxed_2422_: usize = 0;
    let mut v_x_807__boxed_2423_: usize = 0;
    let mut v_res_2424_: *mut LeanObject = core::ptr::null_mut();
    v_x_806__boxed_2422_ = lean_unbox_usize(v_x_2418_);
    lean_dec(v_x_2418_);
    v_x_807__boxed_2423_ = lean_unbox_usize(v_x_2419_);
    lean_dec(v_x_2419_);
    v_res_2424_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg(v_x_2417_, v_x_806__boxed_2422_, v_x_807__boxed_2423_, v_x_2420_, v_x_2421_);
    return v_res_2424_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0___redArg(
    mut v_x_2425_: *mut LeanObject,
    mut v_x_2426_: *mut LeanObject,
    mut v_x_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2429_: u64 = 0;
    let mut v___x_2430_: usize = 0;
    let mut v___x_2431_: usize = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: u64 = 0;
    let mut v_hash_2434_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2426_) == 0 {
                    v___x_2433_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2429_ = v___x_2433_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2434_ = lean_ctor_get_uint64(
                        v_x_2426_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2429_ = v_hash_2434_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2430_ = lean_uint64_to_usize(v___y_2429_);
                v___x_2431_ = 1usize;
                v___x_2432_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg(v_x_2425_, v___x_2430_, v___x_2431_, v_x_2426_, v_x_2427_);
                return v___x_2432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(
    mut v_x_2435_: *mut LeanObject,
    mut v_x_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: u64 = 0;
    let mut v___x_2446_: u64 = 0;
    let mut v___x_2447_: u64 = 0;
    let mut v_fold_2448_: u64 = 0;
    let mut v___x_2449_: u64 = 0;
    let mut v___x_2450_: u64 = 0;
    let mut v___x_2451_: u64 = 0;
    let mut v___x_2452_: usize = 0;
    let mut v___x_2453_: usize = 0;
    let mut v___x_2454_: usize = 0;
    let mut v___x_2455_: usize = 0;
    let mut v___x_2456_: usize = 0;
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u64 = 0;
    let mut v_hash_2464_: u64 = 0;
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2436_) == 0 {
                    return v_x_2435_;
                } else {
                    v_key_2437_ = lean_ctor_get(v_x_2436_, 0);
                    v_value_2438_ = lean_ctor_get(v_x_2436_, 1);
                    v_tail_2439_ = lean_ctor_get(v_x_2436_, 2);
                    v_isSharedCheck_2465_ = (!lean_is_exclusive(v_x_2436_)) as u8;
                    if v_isSharedCheck_2465_ == 0 {
                        v___x_2441_ = v_x_2436_;
                        v_isShared_2442_ = v_isSharedCheck_2465_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2439_);
                        lean_inc(v_value_2438_);
                        lean_inc(v_key_2437_);
                        lean_dec(v_x_2436_);
                        v___x_2441_ = lean_box(0);
                        v_isShared_2442_ = v_isSharedCheck_2465_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2443_ = lean_array_get_size(v_x_2435_);
                if lean_obj_tag(v_key_2437_) == 0 {
                    v___x_2463_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2445_ = v___x_2463_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2464_ = lean_ctor_get_uint64(
                        v_key_2437_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2445_ = v_hash_2464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2446_ = 32u64;
                v___x_2447_ = lean_uint64_shift_right(v___y_2445_, v___x_2446_);
                v_fold_2448_ = lean_uint64_xor(v___y_2445_, v___x_2447_);
                v___x_2449_ = 16u64;
                v___x_2450_ = lean_uint64_shift_right(v_fold_2448_, v___x_2449_);
                v___x_2451_ = lean_uint64_xor(v_fold_2448_, v___x_2450_);
                v___x_2452_ = lean_uint64_to_usize(v___x_2451_);
                v___x_2453_ = lean_usize_of_nat(v___x_2443_);
                v___x_2454_ = 1usize;
                v___x_2455_ = lean_usize_sub(v___x_2453_, v___x_2454_);
                v___x_2456_ = lean_usize_land(v___x_2452_, v___x_2455_);
                v___x_2457_ = lean_array_uget_borrowed(v_x_2435_, v___x_2456_);
                lean_inc(v___x_2457_);
                if v_isShared_2442_ == 0 {
                    lean_ctor_set(v___x_2441_, 2, v___x_2457_);
                    v___x_2459_ = v___x_2441_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_key_2437_);
                    lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_value_2438_);
                    lean_ctor_set(v_reuseFailAlloc_2462_, 2, v___x_2457_);
                    v___x_2459_ = v_reuseFailAlloc_2462_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2460_ = lean_array_uset(v_x_2435_, v___x_2456_, v___x_2459_);
                v_x_2435_ = v___x_2460_;
                v_x_2436_ = v_tail_2439_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(
    mut v_i_2466_: *mut LeanObject,
    mut v_source_2467_: *mut LeanObject,
    mut v_target_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: u8 = 0;
    let mut v_es_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2469_ = lean_array_get_size(v_source_2467_);
                v___x_2470_ = lean_nat_dec_lt(v_i_2466_, v___x_2469_);
                if v___x_2470_ == 0 {
                    lean_dec_ref(v_source_2467_);
                    lean_dec(v_i_2466_);
                    return v_target_2468_;
                } else {
                    v_es_2471_ = lean_array_fget(v_source_2467_, v_i_2466_);
                    v___x_2472_ = lean_box(0);
                    v_source_2473_ = lean_array_fset(v_source_2467_, v_i_2466_, v___x_2472_);
                    v_target_2474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_target_2468_, v_es_2471_);
                    v___x_2475_ = lean_unsigned_to_nat(1);
                    v___x_2476_ = lean_nat_add(v_i_2466_, v___x_2475_);
                    lean_dec(v_i_2466_);
                    v_i_2466_ = v___x_2476_;
                    v_source_2467_ = v_source_2473_;
                    v_target_2468_ = v_target_2474_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4___redArg(
    mut v_data_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    v___x_2479_ = lean_array_get_size(v_data_2478_);
    v___x_2480_ = lean_unsigned_to_nat(2);
    v_nbuckets_2481_ = lean_nat_mul(v___x_2479_, v___x_2480_);
    v___x_2482_ = lean_unsigned_to_nat(0);
    v___x_2483_ = lean_box(0);
    v___x_2484_ = lean_mk_array(v_nbuckets_2481_, v___x_2483_);
    v___x_2485_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v___x_2482_, v_data_2478_, v___x_2484_);
    return v___x_2485_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3___redArg(
    mut v_a_2486_: *mut LeanObject,
    mut v_x_2487_: *mut LeanObject,
) -> u8 {
    let mut v___x_2488_: u8 = 0;
    let mut v_key_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2487_) == 0 {
                    v___x_2488_ = 0;
                    return v___x_2488_;
                } else {
                    v_key_2489_ = lean_ctor_get(v_x_2487_, 0);
                    v_tail_2490_ = lean_ctor_get(v_x_2487_, 2);
                    v___x_2491_ = lean_name_eq(v_key_2489_, v_a_2486_);
                    if v___x_2491_ == 0 {
                        v_x_2487_ = v_tail_2490_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2491_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_2493_: *mut LeanObject,
    mut v_x_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2495_: u8 = 0;
    let mut v_r_2496_: *mut LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3___redArg(v_a_2493_, v_x_2494_);
    lean_dec(v_x_2494_);
    lean_dec(v_a_2493_);
    v_r_2496_ = lean_box((v_res_2495_) as usize);
    return v_r_2496_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__5___redArg(
    mut v_a_2497_: *mut LeanObject,
    mut v_b_2498_: *mut LeanObject,
    mut v_x_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2499_) == 0 {
                    lean_dec(v_b_2498_);
                    lean_dec(v_a_2497_);
                    return v_x_2499_;
                } else {
                    v_key_2500_ = lean_ctor_get(v_x_2499_, 0);
                    v_value_2501_ = lean_ctor_get(v_x_2499_, 1);
                    v_tail_2502_ = lean_ctor_get(v_x_2499_, 2);
                    v_isSharedCheck_2514_ = (!lean_is_exclusive(v_x_2499_)) as u8;
                    if v_isSharedCheck_2514_ == 0 {
                        v___x_2504_ = v_x_2499_;
                        v_isShared_2505_ = v_isSharedCheck_2514_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2502_);
                        lean_inc(v_value_2501_);
                        lean_inc(v_key_2500_);
                        lean_dec(v_x_2499_);
                        v___x_2504_ = lean_box(0);
                        v_isShared_2505_ = v_isSharedCheck_2514_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2506_ = lean_name_eq(v_key_2500_, v_a_2497_);
                if v___x_2506_ == 0 {
                    v___x_2507_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__5___redArg(v_a_2497_, v_b_2498_, v_tail_2502_);
                    if v_isShared_2505_ == 0 {
                        lean_ctor_set(v___x_2504_, 2, v___x_2507_);
                        v___x_2509_ = v___x_2504_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_key_2500_);
                        lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_value_2501_);
                        lean_ctor_set(v_reuseFailAlloc_2510_, 2, v___x_2507_);
                        v___x_2509_ = v_reuseFailAlloc_2510_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2501_);
                    lean_dec(v_key_2500_);
                    if v_isShared_2505_ == 0 {
                        lean_ctor_set(v___x_2504_, 1, v_b_2498_);
                        lean_ctor_set(v___x_2504_, 0, v_a_2497_);
                        v___x_2512_ = v___x_2504_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2497_);
                        lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_b_2498_);
                        lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_tail_2502_);
                        v___x_2512_ = v_reuseFailAlloc_2513_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2509_;
            }
            3 => {
                return v___x_2512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1___redArg(
    mut v_m_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
    mut v_b_2517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2522_: u8 = 0;
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2525_: u64 = 0;
    let mut v___x_2526_: u64 = 0;
    let mut v___x_2527_: u64 = 0;
    let mut v_fold_2528_: u64 = 0;
    let mut v___x_2529_: u64 = 0;
    let mut v___x_2530_: u64 = 0;
    let mut v___x_2531_: u64 = 0;
    let mut v___x_2532_: usize = 0;
    let mut v___x_2533_: usize = 0;
    let mut v___x_2534_: usize = 0;
    let mut v___x_2535_: usize = 0;
    let mut v___x_2536_: usize = 0;
    let mut v_bkt_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v_val_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: u64 = 0;
    let mut v_hash_2564_: u64 = 0;
    let mut v_isSharedCheck_2565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2518_ = lean_ctor_get(v_m_2515_, 0);
                v_buckets_2519_ = lean_ctor_get(v_m_2515_, 1);
                v_isSharedCheck_2565_ = (!lean_is_exclusive(v_m_2515_)) as u8;
                if v_isSharedCheck_2565_ == 0 {
                    v___x_2521_ = v_m_2515_;
                    v_isShared_2522_ = v_isSharedCheck_2565_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2519_);
                    lean_inc(v_size_2518_);
                    lean_dec(v_m_2515_);
                    v___x_2521_ = lean_box(0);
                    v_isShared_2522_ = v_isSharedCheck_2565_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2523_ = lean_array_get_size(v_buckets_2519_);
                if lean_obj_tag(v_a_2516_) == 0 {
                    v___x_2563_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2525_ = v___x_2563_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2564_ = lean_ctor_get_uint64(
                        v_a_2516_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2525_ = v_hash_2564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2526_ = 32u64;
                v___x_2527_ = lean_uint64_shift_right(v___y_2525_, v___x_2526_);
                v_fold_2528_ = lean_uint64_xor(v___y_2525_, v___x_2527_);
                v___x_2529_ = 16u64;
                v___x_2530_ = lean_uint64_shift_right(v_fold_2528_, v___x_2529_);
                v___x_2531_ = lean_uint64_xor(v_fold_2528_, v___x_2530_);
                v___x_2532_ = lean_uint64_to_usize(v___x_2531_);
                v___x_2533_ = lean_usize_of_nat(v___x_2523_);
                v___x_2534_ = 1usize;
                v___x_2535_ = lean_usize_sub(v___x_2533_, v___x_2534_);
                v___x_2536_ = lean_usize_land(v___x_2532_, v___x_2535_);
                v_bkt_2537_ = lean_array_uget_borrowed(v_buckets_2519_, v___x_2536_);
                v___x_2538_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3___redArg(v_a_2516_, v_bkt_2537_);
                if v___x_2538_ == 0 {
                    v___x_2539_ = lean_unsigned_to_nat(1);
                    v_size_x27_2540_ = lean_nat_add(v_size_2518_, v___x_2539_);
                    lean_dec(v_size_2518_);
                    lean_inc(v_bkt_2537_);
                    v___x_2541_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2541_, 0, v_a_2516_);
                    lean_ctor_set(v___x_2541_, 1, v_b_2517_);
                    lean_ctor_set(v___x_2541_, 2, v_bkt_2537_);
                    v_buckets_x27_2542_ =
                        lean_array_uset(v_buckets_2519_, v___x_2536_, v___x_2541_);
                    v___x_2543_ = lean_unsigned_to_nat(4);
                    v___x_2544_ = lean_nat_mul(v_size_x27_2540_, v___x_2543_);
                    v___x_2545_ = lean_unsigned_to_nat(3);
                    v___x_2546_ = lean_nat_div(v___x_2544_, v___x_2545_);
                    lean_dec(v___x_2544_);
                    v___x_2547_ = lean_array_get_size(v_buckets_x27_2542_);
                    v___x_2548_ = lean_nat_dec_le(v___x_2546_, v___x_2547_);
                    lean_dec(v___x_2546_);
                    if v___x_2548_ == 0 {
                        v_val_2549_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4___redArg(v_buckets_x27_2542_);
                        if v_isShared_2522_ == 0 {
                            lean_ctor_set(v___x_2521_, 1, v_val_2549_);
                            lean_ctor_set(v___x_2521_, 0, v_size_x27_2540_);
                            v___x_2551_ = v___x_2521_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_size_x27_2540_);
                            lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_val_2549_);
                            v___x_2551_ = v_reuseFailAlloc_2552_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2522_ == 0 {
                            lean_ctor_set(v___x_2521_, 1, v_buckets_x27_2542_);
                            lean_ctor_set(v___x_2521_, 0, v_size_x27_2540_);
                            v___x_2554_ = v___x_2521_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_size_x27_2540_);
                            lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_buckets_x27_2542_);
                            v___x_2554_ = v_reuseFailAlloc_2555_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2537_);
                    v___x_2556_ = lean_box(0);
                    v_buckets_x27_2557_ =
                        lean_array_uset(v_buckets_2519_, v___x_2536_, v___x_2556_);
                    v___x_2558_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__5___redArg(v_a_2516_, v_b_2517_, v_bkt_2537_);
                    v___x_2559_ = lean_array_uset(v_buckets_x27_2557_, v___x_2536_, v___x_2558_);
                    if v_isShared_2522_ == 0 {
                        lean_ctor_set(v___x_2521_, 1, v___x_2559_);
                        v___x_2561_ = v___x_2521_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_size_2518_);
                        lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2559_);
                        v___x_2561_ = v_reuseFailAlloc_2562_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2551_;
            }
            4 => {
                return v___x_2554_;
            }
            5 => {
                return v___x_2561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0___redArg(
    mut v_x_2566_: *mut LeanObject,
    mut v_x_2567_: *mut LeanObject,
    mut v_x_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_2569_: u8 = 0;
    let mut v_map_u2081_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_map_u2081_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2584_: u8 = 0;
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2569_ = lean_ctor_get_uint8(
                    v_x_2566_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2569_ == 0 {
                    v_map_u2081_2570_ = lean_ctor_get(v_x_2566_, 0);
                    v_map_u2082_2571_ = lean_ctor_get(v_x_2566_, 1);
                    v_isSharedCheck_2579_ = (!lean_is_exclusive(v_x_2566_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v___x_2573_ = v_x_2566_;
                        v_isShared_2574_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_2571_);
                        lean_inc(v_map_u2081_2570_);
                        lean_dec(v_x_2566_);
                        v___x_2573_ = lean_box(0);
                        v_isShared_2574_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_2580_ = lean_ctor_get(v_x_2566_, 0);
                    v_map_u2082_2581_ = lean_ctor_get(v_x_2566_, 1);
                    v_isSharedCheck_2589_ = (!lean_is_exclusive(v_x_2566_)) as u8;
                    if v_isSharedCheck_2589_ == 0 {
                        v___x_2583_ = v_x_2566_;
                        v_isShared_2584_ = v_isSharedCheck_2589_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_2581_);
                        lean_inc(v_map_u2081_2580_);
                        lean_dec(v_x_2566_);
                        v___x_2583_ = lean_box(0);
                        v_isShared_2584_ = v_isSharedCheck_2589_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2575_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0___redArg(v_map_u2082_2571_, v_x_2567_, v_x_2568_);
                if v_isShared_2574_ == 0 {
                    lean_ctor_set(v___x_2573_, 1, v___x_2575_);
                    v___x_2577_ = v___x_2573_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_map_u2081_2570_);
                    lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2575_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2578_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_2569_,
                    );
                    v___x_2577_ = v_reuseFailAlloc_2578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2577_;
            }
            3 => {
                v___x_2585_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1___redArg(v_map_u2081_2580_, v_x_2567_, v_x_2568_);
                if v_isShared_2584_ == 0 {
                    lean_ctor_set(v___x_2583_, 0, v___x_2585_);
                    v___x_2587_ = v___x_2583_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_map_u2082_2581_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2588_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_stage_u2081_2569_,
                    );
                    v___x_2587_ = v_reuseFailAlloc_2588_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ClassState_addEntry(
    mut v_s_2590_: *mut LeanObject,
    mut v_entry_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outParamMap_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outLevelParamMap_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v_name_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outParams_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outLevelParams_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outParamMap_2592_ = lean_ctor_get(v_s_2590_, 0);
                v_outLevelParamMap_2593_ = lean_ctor_get(v_s_2590_, 1);
                v_isSharedCheck_2605_ = (!lean_is_exclusive(v_s_2590_)) as u8;
                if v_isSharedCheck_2605_ == 0 {
                    v___x_2595_ = v_s_2590_;
                    v_isShared_2596_ = v_isSharedCheck_2605_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_outLevelParamMap_2593_);
                    lean_inc(v_outParamMap_2592_);
                    lean_dec(v_s_2590_);
                    v___x_2595_ = lean_box(0);
                    v_isShared_2596_ = v_isSharedCheck_2605_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_name_2597_ = lean_ctor_get(v_entry_2591_, 0);
                lean_inc_n(v_name_2597_, 2);
                v_outParams_2598_ = lean_ctor_get(v_entry_2591_, 1);
                lean_inc_ref(v_outParams_2598_);
                v_outLevelParams_2599_ = lean_ctor_get(v_entry_2591_, 2);
                lean_inc_ref(v_outLevelParams_2599_);
                lean_dec_ref(v_entry_2591_);
                v___x_2600_ = l_Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0___redArg(
                    v_outParamMap_2592_,
                    v_name_2597_,
                    v_outParams_2598_,
                );
                v___x_2601_ = l_Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0___redArg(
                    v_outLevelParamMap_2593_,
                    v_name_2597_,
                    v_outLevelParams_2599_,
                );
                if v_isShared_2596_ == 0 {
                    lean_ctor_set(v___x_2595_, 1, v___x_2601_);
                    lean_ctor_set(v___x_2595_, 0, v___x_2600_);
                    v___x_2603_ = v___x_2595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2600_);
                    lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0(
    mut v_00_u03b2_2606_: *mut LeanObject,
    mut v_x_2607_: *mut LeanObject,
    mut v_x_2608_: *mut LeanObject,
    mut v_x_2609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    v___x_2610_ = l_Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0___redArg(
        v_x_2607_, v_x_2608_, v_x_2609_,
    );
    return v___x_2610_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0(
    mut v_00_u03b2_2611_: *mut LeanObject,
    mut v_x_2612_: *mut LeanObject,
    mut v_x_2613_: *mut LeanObject,
    mut v_x_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    v___x_2615_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0___redArg(v_x_2612_, v_x_2613_, v_x_2614_);
    return v___x_2615_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1(
    mut v_00_u03b2_2616_: *mut LeanObject,
    mut v_m_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
    mut v_b_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    v___x_2620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1___redArg(v_m_2617_, v_a_2618_, v_b_2619_);
    return v___x_2620_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2621_: *mut LeanObject,
    mut v_x_2622_: *mut LeanObject,
    mut v_x_2623_: usize,
    mut v_x_2624_: usize,
    mut v_x_2625_: *mut LeanObject,
    mut v_x_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    v___x_2627_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg(v_x_2622_, v_x_2623_, v_x_2624_, v_x_2625_, v_x_2626_);
    return v___x_2627_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2628_: *mut LeanObject,
    mut v_x_2629_: *mut LeanObject,
    mut v_x_2630_: *mut LeanObject,
    mut v_x_2631_: *mut LeanObject,
    mut v_x_2632_: *mut LeanObject,
    mut v_x_2633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1295__boxed_2634_: usize = 0;
    let mut v_x_1296__boxed_2635_: usize = 0;
    let mut v_res_2636_: *mut LeanObject = core::ptr::null_mut();
    v_x_1295__boxed_2634_ = lean_unbox_usize(v_x_2630_);
    lean_dec(v_x_2630_);
    v_x_1296__boxed_2635_ = lean_unbox_usize(v_x_2631_);
    lean_dec(v_x_2631_);
    v_res_2636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1(v_00_u03b2_2628_, v_x_2629_, v_x_1295__boxed_2634_, v_x_1296__boxed_2635_, v_x_2632_, v_x_2633_);
    return v_res_2636_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_x_2639_: *mut LeanObject,
) -> u8 {
    let mut v___x_2640_: u8 = 0;
    v___x_2640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3___redArg(v_a_2638_, v_x_2639_);
    return v___x_2640_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_x_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2644_: u8 = 0;
    let mut v_r_2645_: *mut LeanObject = core::ptr::null_mut();
    v_res_2644_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3(v_00_u03b2_2641_, v_a_2642_, v_x_2643_);
    lean_dec(v_x_2643_);
    lean_dec(v_a_2642_);
    v_r_2645_ = lean_box((v_res_2644_) as usize);
    return v_r_2645_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4(
    mut v_00_u03b2_2646_: *mut LeanObject,
    mut v_data_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    v___x_2648_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4___redArg(v_data_2647_);
    return v___x_2648_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__5(
    mut v_00_u03b2_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
    mut v_b_2651_: *mut LeanObject,
    mut v_x_2652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    v___x_2653_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__5___redArg(v_a_2650_, v_b_2651_, v_x_2652_);
    return v___x_2653_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2654_: *mut LeanObject,
    mut v_n_2655_: *mut LeanObject,
    mut v_k_2656_: *mut LeanObject,
    mut v_v_2657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2655_, v_k_2656_, v_v_2657_);
    return v___x_2658_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2659_: *mut LeanObject,
    mut v_depth_2660_: usize,
    mut v_keys_2661_: *mut LeanObject,
    mut v_vals_2662_: *mut LeanObject,
    mut v_heq_2663_: *mut LeanObject,
    mut v_i_2664_: *mut LeanObject,
    mut v_entries_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    v___x_2666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_2660_, v_keys_2661_, v_vals_2662_, v_i_2664_, v_entries_2665_);
    return v___x_2666_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2667_: *mut LeanObject,
    mut v_depth_2668_: *mut LeanObject,
    mut v_keys_2669_: *mut LeanObject,
    mut v_vals_2670_: *mut LeanObject,
    mut v_heq_2671_: *mut LeanObject,
    mut v_i_2672_: *mut LeanObject,
    mut v_entries_2673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2674_: usize = 0;
    let mut v_res_2675_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2674_ = lean_unbox_usize(v_depth_2668_);
    lean_dec(v_depth_2668_);
    v_res_2675_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_2667_, v_depth_boxed_2674_, v_keys_2669_, v_vals_2670_, v_heq_2671_, v_i_2672_, v_entries_2673_);
    lean_dec_ref(v_vals_2670_);
    lean_dec_ref(v_keys_2669_);
    return v_res_2675_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_2676_: *mut LeanObject,
    mut v_i_2677_: *mut LeanObject,
    mut v_source_2678_: *mut LeanObject,
    mut v_target_2679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    v___x_2680_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7___redArg(v_i_2677_, v_source_2678_, v_target_2679_);
    return v___x_2680_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2681_: *mut LeanObject,
    mut v_x_2682_: *mut LeanObject,
    mut v_x_2683_: *mut LeanObject,
    mut v_x_2684_: *mut LeanObject,
    mut v_x_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    v___x_2686_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_x_2682_, v_x_2683_, v_x_2684_, v_x_2685_);
    return v___x_2686_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v_00_u03b2_2687_: *mut LeanObject,
    mut v_x_2688_: *mut LeanObject,
    mut v_x_2689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    v___x_2690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__4_spec__7_spec__9___redArg(v_x_2688_, v_x_2689_);
    return v___x_2690_;
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_ClassState_switch_spec__0___redArg(
    mut v_m_2691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_2692_: u8 = 0;
    let mut v_map_u2081_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2692_ = lean_ctor_get_uint8(
                    v_m_2691_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2692_ == 0 {
                    return v_m_2691_;
                } else {
                    v_map_u2081_2693_ = lean_ctor_get(v_m_2691_, 0);
                    v_map_u2082_2694_ = lean_ctor_get(v_m_2691_, 1);
                    v_isSharedCheck_2702_ = (!lean_is_exclusive(v_m_2691_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2696_ = v_m_2691_;
                        v_isShared_2697_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_2694_);
                        lean_inc(v_map_u2081_2693_);
                        lean_dec(v_m_2691_);
                        v___x_2696_ = lean_box(0);
                        v_isShared_2697_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2698_ = 0;
                if v_isShared_2697_ == 0 {
                    v___x_2700_ = v___x_2696_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_map_u2081_2693_);
                    lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_map_u2082_2694_);
                    v___x_2700_ = v_reuseFailAlloc_2701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2700_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2698_,
                );
                return v___x_2700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00Lean_ClassState_switch_spec__0(
    mut v_00_u03b2_2703_: *mut LeanObject,
    mut v_m_2704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Lean_SMap_switch___at___00Lean_ClassState_switch_spec__0___redArg(v_m_2704_);
    return v___x_2705_;
}
pub unsafe fn l_Lean_ClassState_switch(mut v_s_2706_: *mut LeanObject) -> *mut LeanObject {
    let mut v_outParamMap_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outLevelParamMap_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2711_: u8 = 0;
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outParamMap_2707_ = lean_ctor_get(v_s_2706_, 0);
                v_outLevelParamMap_2708_ = lean_ctor_get(v_s_2706_, 1);
                v_isSharedCheck_2717_ = (!lean_is_exclusive(v_s_2706_)) as u8;
                if v_isSharedCheck_2717_ == 0 {
                    v___x_2710_ = v_s_2706_;
                    v_isShared_2711_ = v_isSharedCheck_2717_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_outLevelParamMap_2708_);
                    lean_inc(v_outParamMap_2707_);
                    lean_dec(v_s_2706_);
                    v___x_2710_ = lean_box(0);
                    v_isShared_2711_ = v_isSharedCheck_2717_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2712_ = l_Lean_SMap_switch___at___00Lean_ClassState_switch_spec__0___redArg(
                    v_outParamMap_2707_,
                );
                v___x_2713_ = l_Lean_SMap_switch___at___00Lean_ClassState_switch_spec__0___redArg(
                    v_outLevelParamMap_2708_,
                );
                if v_isShared_2711_ == 0 {
                    lean_ctor_set(v___x_2710_, 1, v___x_2713_);
                    lean_ctor_set(v___x_2710_, 0, v___x_2712_);
                    v___x_2715_ = v___x_2710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2716_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2712_);
                    lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2713_);
                    v___x_2715_ = v_reuseFailAlloc_2716_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn___lam__0_00___x40_Lean_Class_903839608____hygCtx___hyg_2_(
    mut v_es_2718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    v___x_2719_ = lean_array_mk(v_es_2718_);
    return v___x_2719_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_2720_: *mut LeanObject,
    mut v_i_2721_: usize,
    mut v_stop_2722_: usize,
    mut v_b_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2724_: u8 = 0;
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: usize = 0;
    let mut v___x_2728_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2724_ = lean_usize_dec_eq(v_i_2721_, v_stop_2722_);
                if v___x_2724_ == 0 {
                    v___x_2725_ = lean_array_uget_borrowed(v_as_2720_, v_i_2721_);
                    lean_inc(v___x_2725_);
                    v___x_2726_ = l_Lean_ClassState_addEntry(v_b_2723_, v___x_2725_);
                    v___x_2727_ = 1usize;
                    v___x_2728_ = lean_usize_add(v_i_2721_, v___x_2727_);
                    v_i_2721_ = v___x_2728_;
                    v_b_2723_ = v___x_2726_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2723_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_2730_: *mut LeanObject,
    mut v_i_2731_: *mut LeanObject,
    mut v_stop_2732_: *mut LeanObject,
    mut v_b_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2734_: usize = 0;
    let mut v_stop_boxed_2735_: usize = 0;
    let mut v_res_2736_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2734_ = lean_unbox_usize(v_i_2731_);
    lean_dec(v_i_2731_);
    v_stop_boxed_2735_ = lean_unbox_usize(v_stop_2732_);
    lean_dec(v_stop_2732_);
    v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__0(v_as_2730_, v_i_boxed_2734_, v_stop_boxed_2735_, v_b_2733_);
    lean_dec_ref(v_as_2730_);
    return v_res_2736_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_2737_: *mut LeanObject,
    mut v_i_2738_: usize,
    mut v_stop_2739_: usize,
    mut v_b_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: usize = 0;
    let mut v___x_2744_: usize = 0;
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: u8 = 0;
    let mut v___x_2752_: usize = 0;
    let mut v___x_2753_: usize = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: usize = 0;
    let mut v___x_2756_: usize = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = lean_usize_dec_eq(v_i_2738_, v_stop_2739_);
                if v___x_2746_ == 0 {
                    v___x_2747_ = lean_array_uget_borrowed(v_as_2737_, v_i_2738_);
                    v___x_2748_ = lean_unsigned_to_nat(0);
                    v___x_2749_ = lean_array_get_size(v___x_2747_);
                    v___x_2750_ = lean_nat_dec_lt(v___x_2748_, v___x_2749_);
                    if v___x_2750_ == 0 {
                        v___y_2742_ = v_b_2740_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2751_ = lean_nat_dec_le(v___x_2749_, v___x_2749_);
                        if v___x_2751_ == 0 {
                            if v___x_2750_ == 0 {
                                v___y_2742_ = v_b_2740_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2752_ = 0usize;
                                v___x_2753_ = lean_usize_of_nat(v___x_2749_);
                                v___x_2754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__0(v___x_2747_, v___x_2752_, v___x_2753_, v_b_2740_);
                                v___y_2742_ = v___x_2754_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2755_ = 0usize;
                            v___x_2756_ = lean_usize_of_nat(v___x_2749_);
                            v___x_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__0(v___x_2747_, v___x_2755_, v___x_2756_, v_b_2740_);
                            v___y_2742_ = v___x_2757_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_2740_;
                }
            }
            1 => {
                v___x_2743_ = 1usize;
                v___x_2744_ = lean_usize_add(v_i_2738_, v___x_2743_);
                v_i_2738_ = v___x_2744_;
                v_b_2740_ = v___y_2742_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_as_2758_: *mut LeanObject,
    mut v_i_2759_: *mut LeanObject,
    mut v_stop_2760_: *mut LeanObject,
    mut v_b_2761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2762_: usize = 0;
    let mut v_stop_boxed_2763_: usize = 0;
    let mut v_res_2764_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2762_ = lean_unbox_usize(v_i_2759_);
    lean_dec(v_i_2759_);
    v_stop_boxed_2763_ = lean_unbox_usize(v_stop_2760_);
    lean_dec(v_stop_2760_);
    v_res_2764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__1(v_as_2758_, v_i_boxed_2762_, v_stop_boxed_2763_, v_b_2761_);
    lean_dec_ref(v_as_2758_);
    return v_res_2764_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0(
    mut v_initState_2765_: *mut LeanObject,
    mut v_as_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    v___x_2767_ = lean_unsigned_to_nat(0);
    v___x_2768_ = lean_array_get_size(v_as_2766_);
    v___x_2769_ = lean_nat_dec_lt(v___x_2767_, v___x_2768_);
    if v___x_2769_ == 0 {
        return v_initState_2765_;
    } else {
        let mut v___x_2770_: u8 = 0;
        v___x_2770_ = lean_nat_dec_le(v___x_2768_, v___x_2768_);
        if v___x_2770_ == 0 {
            if v___x_2769_ == 0 {
                return v_initState_2765_;
            } else {
                let mut v___x_2771_: usize = 0;
                let mut v___x_2772_: usize = 0;
                let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
                v___x_2771_ = 0usize;
                v___x_2772_ = lean_usize_of_nat(v___x_2768_);
                v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__1(v_as_2766_, v___x_2771_, v___x_2772_, v_initState_2765_);
                return v___x_2773_;
            }
        } else {
            let mut v___x_2774_: usize = 0;
            let mut v___x_2775_: usize = 0;
            let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
            v___x_2774_ = 0usize;
            v___x_2775_ = lean_usize_of_nat(v___x_2768_);
            v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0_spec__1(v_as_2766_, v___x_2774_, v___x_2775_, v_initState_2765_);
            return v___x_2776_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_2777_: *mut LeanObject,
    mut v_as_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2779_: *mut LeanObject = core::ptr::null_mut();
    v_res_2779_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0(v_initState_2777_, v_as_2778_);
    lean_dec_ref(v_as_2778_);
    return v_res_2779_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2_(
    mut v_es_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    v___x_2781_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClassState_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedClassState_default___closed__1_once),
        _init_l_Lean_instInhabitedClassState_default___closed__1,
    );
    v___x_2782_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2__spec__0(v___x_2781_, v_es_2780_);
    v___x_2783_ = l_Lean_ClassState_switch(v___x_2782_);
    return v___x_2783_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2____boxed(
    mut v_es_2784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2785_: *mut LeanObject = core::ptr::null_mut();
    v_res_2785_ = l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_903839608____hygCtx___hyg_2_(v_es_2784_);
    lean_dec_ref(v_es_2784_);
    return v_res_2785_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    v___x_2802_ = l___private_Lean_Class_0__Lean_initFn___closed__6_00___x40_Lean_Class_903839608____hygCtx___hyg_2_;
    v___x_2803_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_2802_);
    return v___x_2803_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2____boxed(
    mut v_a_2804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2805_: *mut LeanObject = core::ptr::null_mut();
    v_res_2805_ =
        l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2_();
    return v_res_2805_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(
    mut v_m_2806_: *mut LeanObject,
    mut v_a_2807_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: u64 = 0;
    let mut v___x_2812_: u64 = 0;
    let mut v___x_2813_: u64 = 0;
    let mut v_fold_2814_: u64 = 0;
    let mut v___x_2815_: u64 = 0;
    let mut v___x_2816_: u64 = 0;
    let mut v___x_2817_: u64 = 0;
    let mut v___x_2818_: usize = 0;
    let mut v___x_2819_: usize = 0;
    let mut v___x_2820_: usize = 0;
    let mut v___x_2821_: usize = 0;
    let mut v___x_2822_: usize = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: u64 = 0;
    let mut v_hash_2826_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2808_ = lean_ctor_get(v_m_2806_, 1);
                v___x_2809_ = lean_array_get_size(v_buckets_2808_);
                if lean_obj_tag(v_a_2807_) == 0 {
                    v___x_2825_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2811_ = v___x_2825_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2826_ = lean_ctor_get_uint64(
                        v_a_2807_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2811_ = v_hash_2826_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2812_ = 32u64;
                v___x_2813_ = lean_uint64_shift_right(v___y_2811_, v___x_2812_);
                v_fold_2814_ = lean_uint64_xor(v___y_2811_, v___x_2813_);
                v___x_2815_ = 16u64;
                v___x_2816_ = lean_uint64_shift_right(v_fold_2814_, v___x_2815_);
                v___x_2817_ = lean_uint64_xor(v_fold_2814_, v___x_2816_);
                v___x_2818_ = lean_uint64_to_usize(v___x_2817_);
                v___x_2819_ = lean_usize_of_nat(v___x_2809_);
                v___x_2820_ = 1usize;
                v___x_2821_ = lean_usize_sub(v___x_2819_, v___x_2820_);
                v___x_2822_ = lean_usize_land(v___x_2818_, v___x_2821_);
                v___x_2823_ = lean_array_uget_borrowed(v_buckets_2808_, v___x_2822_);
                v___x_2824_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__1_spec__3___redArg(v_a_2807_, v___x_2823_);
                return v___x_2824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg___boxed(
    mut v_m_2827_: *mut LeanObject,
    mut v_a_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2829_: u8 = 0;
    let mut v_r_2830_: *mut LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(v_m_2827_, v_a_2828_);
    lean_dec(v_a_2828_);
    lean_dec_ref(v_m_2827_);
    v_r_2830_ = lean_box((v_res_2829_) as usize);
    return v_r_2830_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_keys_2831_: *mut LeanObject,
    mut v_i_2832_: *mut LeanObject,
    mut v_k_2833_: *mut LeanObject,
) -> u8 {
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v_k_x27_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2834_ = lean_array_get_size(v_keys_2831_);
                v___x_2835_ = lean_nat_dec_lt(v_i_2832_, v___x_2834_);
                if v___x_2835_ == 0 {
                    lean_dec(v_i_2832_);
                    return v___x_2835_;
                } else {
                    v_k_x27_2836_ = lean_array_fget_borrowed(v_keys_2831_, v_i_2832_);
                    v___x_2837_ = lean_name_eq(v_k_2833_, v_k_x27_2836_);
                    if v___x_2837_ == 0 {
                        v___x_2838_ = lean_unsigned_to_nat(1);
                        v___x_2839_ = lean_nat_add(v_i_2832_, v___x_2838_);
                        lean_dec(v_i_2832_);
                        v_i_2832_ = v___x_2839_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_2832_);
                        return v___x_2837_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_2841_: *mut LeanObject,
    mut v_i_2842_: *mut LeanObject,
    mut v_k_2843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2844_: u8 = 0;
    let mut v_r_2845_: *mut LeanObject = core::ptr::null_mut();
    v_res_2844_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2841_, v_i_2842_, v_k_2843_);
    lean_dec(v_k_2843_);
    lean_dec_ref(v_keys_2841_);
    v_r_2845_ = lean_box((v_res_2844_) as usize);
    return v_r_2845_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2___redArg(
    mut v_x_2846_: *mut LeanObject,
    mut v_x_2847_: usize,
    mut v_x_2848_: *mut LeanObject,
) -> u8 {
    let mut v_es_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: usize = 0;
    let mut v___x_2852_: usize = 0;
    let mut v___x_2853_: usize = 0;
    let mut v_j_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut v_node_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: usize = 0;
    let mut v___x_2861_: u8 = 0;
    let mut v_ks_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2846_) == 0 {
                    v_es_2849_ = lean_ctor_get(v_x_2846_, 0);
                    v___x_2850_ = lean_box(2);
                    v___x_2851_ = 5usize;
                    v___x_2852_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2853_ = lean_usize_land(v_x_2847_, v___x_2852_);
                    v_j_2854_ = lean_usize_to_nat(v___x_2853_);
                    v___x_2855_ = lean_array_get_borrowed(v___x_2850_, v_es_2849_, v_j_2854_);
                    lean_dec(v_j_2854_);
                    match lean_obj_tag(v___x_2855_) {
                        0 => {
                            v_key_2856_ = lean_ctor_get(v___x_2855_, 0);
                            v___x_2857_ = lean_name_eq(v_x_2848_, v_key_2856_);
                            return v___x_2857_;
                        }
                        1 => {
                            v_node_2858_ = lean_ctor_get(v___x_2855_, 0);
                            v___x_2859_ = lean_usize_shift_right(v_x_2847_, v___x_2851_);
                            v_x_2846_ = v_node_2858_;
                            v_x_2847_ = v___x_2859_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2861_ = 0;
                            return v___x_2861_;
                        }
                    }
                } else {
                    v_ks_2862_ = lean_ctor_get(v_x_2846_, 0);
                    v___x_2863_ = lean_unsigned_to_nat(0);
                    v___x_2864_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_2862_, v___x_2863_, v_x_2848_);
                    return v___x_2864_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_x_2865_: *mut LeanObject,
    mut v_x_2866_: *mut LeanObject,
    mut v_x_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_266__boxed_2868_: usize = 0;
    let mut v_res_2869_: u8 = 0;
    let mut v_r_2870_: *mut LeanObject = core::ptr::null_mut();
    v_x_266__boxed_2868_ = lean_unbox_usize(v_x_2866_);
    lean_dec(v_x_2866_);
    v_res_2869_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2___redArg(v_x_2865_, v_x_266__boxed_2868_, v_x_2867_);
    lean_dec(v_x_2867_);
    lean_dec_ref(v_x_2865_);
    v_r_2870_ = lean_box((v_res_2869_) as usize);
    return v_r_2870_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1___redArg(
    mut v_x_2871_: *mut LeanObject,
    mut v_x_2872_: *mut LeanObject,
) -> u8 {
    let mut v___y_2874_: u64 = 0;
    let mut v___x_2875_: usize = 0;
    let mut v___x_2876_: u8 = 0;
    let mut v___x_2877_: u64 = 0;
    let mut v_hash_2878_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2872_) == 0 {
                    v___x_2877_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2874_ = v___x_2877_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2878_ = lean_ctor_get_uint64(
                        v_x_2872_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2874_ = v_hash_2878_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2875_ = lean_uint64_to_usize(v___y_2874_);
                v___x_2876_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2___redArg(v_x_2871_, v___x_2875_, v_x_2872_);
                return v___x_2876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1___redArg___boxed(
    mut v_x_2879_: *mut LeanObject,
    mut v_x_2880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2881_: u8 = 0;
    let mut v_r_2882_: *mut LeanObject = core::ptr::null_mut();
    v_res_2881_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1___redArg(v_x_2879_, v_x_2880_);
    lean_dec(v_x_2880_);
    lean_dec_ref(v_x_2879_);
    v_r_2882_ = lean_box((v_res_2881_) as usize);
    return v_r_2882_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_isClass_spec__0___redArg(
    mut v_x_2883_: *mut LeanObject,
    mut v_x_2884_: *mut LeanObject,
) -> u8 {
    let mut v_stage_u2081_2885_: u8 = 0;
    v_stage_u2081_2885_ = lean_ctor_get_uint8(
        v_x_2883_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_2885_ == 0 {
        let mut v_map_u2081_2886_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_2887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2888_: u8 = 0;
        v_map_u2081_2886_ = lean_ctor_get(v_x_2883_, 0);
        v_map_u2082_2887_ = lean_ctor_get(v_x_2883_, 1);
        v___x_2888_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(v_map_u2081_2886_, v_x_2884_);
        if v___x_2888_ == 0 {
            let mut v___x_2889_: u8 = 0;
            v___x_2889_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1___redArg(v_map_u2082_2887_, v_x_2884_);
            return v___x_2889_;
        } else {
            return v___x_2888_;
        }
    } else {
        let mut v_map_u2081_2890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: u8 = 0;
        v_map_u2081_2890_ = lean_ctor_get(v_x_2883_, 0);
        v___x_2891_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(v_map_u2081_2890_, v_x_2884_);
        return v___x_2891_;
    }
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_isClass_spec__0___redArg___boxed(
    mut v_x_2892_: *mut LeanObject,
    mut v_x_2893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2894_: u8 = 0;
    let mut v_r_2895_: *mut LeanObject = core::ptr::null_mut();
    v_res_2894_ = l_Lean_SMap_contains___at___00Lean_isClass_spec__0___redArg(v_x_2892_, v_x_2893_);
    lean_dec(v_x_2893_);
    lean_dec_ref(v_x_2892_);
    v_r_2895_ = lean_box((v_res_2894_) as usize);
    return v_r_2895_;
}
pub unsafe fn lean_is_class(
    mut v_env_2896_: *mut LeanObject,
    mut v_n_2897_: *mut LeanObject,
) -> u8 {
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outParamMap_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: u8 = 0;
    v___x_2898_ = l_Lean_classExtension;
    v_toEnvExtension_2899_ = lean_ctor_get(v___x_2898_, 0);
    v_asyncMode_2900_ = lean_ctor_get(v_toEnvExtension_2899_, 2);
    v___x_2901_ = l_Lean_instInhabitedClassState_default;
    v___x_2902_ = lean_box(0);
    v___x_2903_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_2901_,
        v___x_2898_,
        v_env_2896_,
        v_asyncMode_2900_,
        v___x_2902_,
    );
    v_outParamMap_2904_ = lean_ctor_get(v___x_2903_, 0);
    lean_inc_ref(v_outParamMap_2904_);
    lean_dec(v___x_2903_);
    v___x_2905_ =
        l_Lean_SMap_contains___at___00Lean_isClass_spec__0___redArg(v_outParamMap_2904_, v_n_2897_);
    lean_dec(v_n_2897_);
    lean_dec_ref(v_outParamMap_2904_);
    return v___x_2905_;
}
pub unsafe fn l_Lean_isClass___boxed(
    mut v_env_2906_: *mut LeanObject,
    mut v_n_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2908_: u8 = 0;
    let mut v_r_2909_: *mut LeanObject = core::ptr::null_mut();
    v_res_2908_ = lean_is_class(v_env_2906_, v_n_2907_);
    v_r_2909_ = lean_box((v_res_2908_) as usize);
    return v_r_2909_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_isClass_spec__0(
    mut v_00_u03b2_2910_: *mut LeanObject,
    mut v_x_2911_: *mut LeanObject,
    mut v_x_2912_: *mut LeanObject,
) -> u8 {
    let mut v___x_2913_: u8 = 0;
    v___x_2913_ = l_Lean_SMap_contains___at___00Lean_isClass_spec__0___redArg(v_x_2911_, v_x_2912_);
    return v___x_2913_;
}
pub unsafe fn l_Lean_SMap_contains___at___00Lean_isClass_spec__0___boxed(
    mut v_00_u03b2_2914_: *mut LeanObject,
    mut v_x_2915_: *mut LeanObject,
    mut v_x_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2917_: u8 = 0;
    let mut v_r_2918_: *mut LeanObject = core::ptr::null_mut();
    v_res_2917_ =
        l_Lean_SMap_contains___at___00Lean_isClass_spec__0(v_00_u03b2_2914_, v_x_2915_, v_x_2916_);
    lean_dec(v_x_2916_);
    lean_dec_ref(v_x_2915_);
    v_r_2918_ = lean_box((v_res_2917_) as usize);
    return v_r_2918_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0(
    mut v_00_u03b2_2919_: *mut LeanObject,
    mut v_m_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
) -> u8 {
    let mut v___x_2922_: u8 = 0;
    v___x_2922_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___redArg(v_m_2920_, v_a_2921_);
    return v___x_2922_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0___boxed(
    mut v_00_u03b2_2923_: *mut LeanObject,
    mut v_m_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2926_: u8 = 0;
    let mut v_r_2927_: *mut LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__0(v_00_u03b2_2923_, v_m_2924_, v_a_2925_);
    lean_dec(v_a_2925_);
    lean_dec_ref(v_m_2924_);
    v_r_2927_ = lean_box((v_res_2926_) as usize);
    return v_r_2927_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1(
    mut v_00_u03b2_2928_: *mut LeanObject,
    mut v_x_2929_: *mut LeanObject,
    mut v_x_2930_: *mut LeanObject,
) -> u8 {
    let mut v___x_2931_: u8 = 0;
    v___x_2931_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1___redArg(v_x_2929_, v_x_2930_);
    return v___x_2931_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1___boxed(
    mut v_00_u03b2_2932_: *mut LeanObject,
    mut v_x_2933_: *mut LeanObject,
    mut v_x_2934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2935_: u8 = 0;
    let mut v_r_2936_: *mut LeanObject = core::ptr::null_mut();
    v_res_2935_ = l_Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1(v_00_u03b2_2932_, v_x_2933_, v_x_2934_);
    lean_dec(v_x_2934_);
    lean_dec_ref(v_x_2933_);
    v_r_2936_ = lean_box((v_res_2935_) as usize);
    return v_r_2936_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2937_: *mut LeanObject,
    mut v_x_2938_: *mut LeanObject,
    mut v_x_2939_: usize,
    mut v_x_2940_: *mut LeanObject,
) -> u8 {
    let mut v___x_2941_: u8 = 0;
    v___x_2941_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2___redArg(v_x_2938_, v_x_2939_, v_x_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_2942_: *mut LeanObject,
    mut v_x_2943_: *mut LeanObject,
    mut v_x_2944_: *mut LeanObject,
    mut v_x_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_376__boxed_2946_: usize = 0;
    let mut v_res_2947_: u8 = 0;
    let mut v_r_2948_: *mut LeanObject = core::ptr::null_mut();
    v_x_376__boxed_2946_ = lean_unbox_usize(v_x_2944_);
    lean_dec(v_x_2944_);
    v_res_2947_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2(v_00_u03b2_2942_, v_x_2943_, v_x_376__boxed_2946_, v_x_2945_);
    lean_dec(v_x_2945_);
    lean_dec_ref(v_x_2943_);
    v_r_2948_ = lean_box((v_res_2947_) as usize);
    return v_r_2948_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2949_: *mut LeanObject,
    mut v_keys_2950_: *mut LeanObject,
    mut v_vals_2951_: *mut LeanObject,
    mut v_heq_2952_: *mut LeanObject,
    mut v_i_2953_: *mut LeanObject,
    mut v_k_2954_: *mut LeanObject,
) -> u8 {
    let mut v___x_2955_: u8 = 0;
    v___x_2955_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2950_, v_i_2953_, v_k_2954_);
    return v___x_2955_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_2956_: *mut LeanObject,
    mut v_keys_2957_: *mut LeanObject,
    mut v_vals_2958_: *mut LeanObject,
    mut v_heq_2959_: *mut LeanObject,
    mut v_i_2960_: *mut LeanObject,
    mut v_k_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2962_: u8 = 0;
    let mut v_r_2963_: *mut LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_SMap_contains___at___00Lean_isClass_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_2956_, v_keys_2957_, v_vals_2958_, v_heq_2959_, v_i_2960_, v_k_2961_);
    lean_dec(v_k_2961_);
    lean_dec_ref(v_vals_2958_);
    lean_dec_ref(v_keys_2957_);
    v_r_2963_ = lean_box((v_res_2962_) as usize);
    return v_r_2963_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3___redArg(
    mut v_a_2964_: *mut LeanObject,
    mut v_x_2965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2965_) == 0 {
                    v___x_2966_ = lean_box(0);
                    return v___x_2966_;
                } else {
                    v_key_2967_ = lean_ctor_get(v_x_2965_, 0);
                    v_value_2968_ = lean_ctor_get(v_x_2965_, 1);
                    v_tail_2969_ = lean_ctor_get(v_x_2965_, 2);
                    v___x_2970_ = lean_name_eq(v_key_2967_, v_a_2964_);
                    if v___x_2970_ == 0 {
                        v_x_2965_ = v_tail_2969_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2968_);
                        v___x_2972_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2972_, 0, v_value_2968_);
                        return v___x_2972_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_2973_: *mut LeanObject,
    mut v_x_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2975_: *mut LeanObject = core::ptr::null_mut();
    v_res_2975_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3___redArg(v_a_2973_, v_x_2974_);
    lean_dec(v_x_2974_);
    lean_dec(v_a_2973_);
    return v_res_2975_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1___redArg(
    mut v_m_2976_: *mut LeanObject,
    mut v_a_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2981_: u64 = 0;
    let mut v___x_2982_: u64 = 0;
    let mut v___x_2983_: u64 = 0;
    let mut v_fold_2984_: u64 = 0;
    let mut v___x_2985_: u64 = 0;
    let mut v___x_2986_: u64 = 0;
    let mut v___x_2987_: u64 = 0;
    let mut v___x_2988_: usize = 0;
    let mut v___x_2989_: usize = 0;
    let mut v___x_2990_: usize = 0;
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: usize = 0;
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: u64 = 0;
    let mut v_hash_2996_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2978_ = lean_ctor_get(v_m_2976_, 1);
                v___x_2979_ = lean_array_get_size(v_buckets_2978_);
                if lean_obj_tag(v_a_2977_) == 0 {
                    v___x_2995_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_2981_ = v___x_2995_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2996_ = lean_ctor_get_uint64(
                        v_a_2977_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_2981_ = v_hash_2996_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2982_ = 32u64;
                v___x_2983_ = lean_uint64_shift_right(v___y_2981_, v___x_2982_);
                v_fold_2984_ = lean_uint64_xor(v___y_2981_, v___x_2983_);
                v___x_2985_ = 16u64;
                v___x_2986_ = lean_uint64_shift_right(v_fold_2984_, v___x_2985_);
                v___x_2987_ = lean_uint64_xor(v_fold_2984_, v___x_2986_);
                v___x_2988_ = lean_uint64_to_usize(v___x_2987_);
                v___x_2989_ = lean_usize_of_nat(v___x_2979_);
                v___x_2990_ = 1usize;
                v___x_2991_ = lean_usize_sub(v___x_2989_, v___x_2990_);
                v___x_2992_ = lean_usize_land(v___x_2988_, v___x_2991_);
                v___x_2993_ = lean_array_uget_borrowed(v_buckets_2978_, v___x_2992_);
                v___x_2994_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3___redArg(v_a_2977_, v___x_2993_);
                return v___x_2994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1___redArg___boxed(
    mut v_m_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1___redArg(v_m_2997_, v_a_2998_);
    lean_dec(v_a_2998_);
    lean_dec_ref(v_m_2997_);
    return v_res_2999_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_keys_3000_: *mut LeanObject,
    mut v_vals_3001_: *mut LeanObject,
    mut v_i_3002_: *mut LeanObject,
    mut v_k_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: u8 = 0;
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3004_ = lean_array_get_size(v_keys_3000_);
                v___x_3005_ = lean_nat_dec_lt(v_i_3002_, v___x_3004_);
                if v___x_3005_ == 0 {
                    lean_dec(v_i_3002_);
                    v___x_3006_ = lean_box(0);
                    return v___x_3006_;
                } else {
                    v_k_x27_3007_ = lean_array_fget_borrowed(v_keys_3000_, v_i_3002_);
                    v___x_3008_ = lean_name_eq(v_k_3003_, v_k_x27_3007_);
                    if v___x_3008_ == 0 {
                        v___x_3009_ = lean_unsigned_to_nat(1);
                        v___x_3010_ = lean_nat_add(v_i_3002_, v___x_3009_);
                        lean_dec(v_i_3002_);
                        v_i_3002_ = v___x_3010_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3012_ = lean_array_fget_borrowed(v_vals_3001_, v_i_3002_);
                        lean_dec(v_i_3002_);
                        lean_inc(v___x_3012_);
                        v___x_3013_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3013_, 0, v___x_3012_);
                        return v___x_3013_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_keys_3014_: *mut LeanObject,
    mut v_vals_3015_: *mut LeanObject,
    mut v_i_3016_: *mut LeanObject,
    mut v_k_3017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3018_: *mut LeanObject = core::ptr::null_mut();
    v_res_3018_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_3014_, v_vals_3015_, v_i_3016_, v_k_3017_);
    lean_dec(v_k_3017_);
    lean_dec_ref(v_vals_3015_);
    lean_dec_ref(v_keys_3014_);
    return v_res_3018_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_x_3019_: *mut LeanObject,
    mut v_x_3020_: usize,
    mut v_x_3021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: usize = 0;
    let mut v___x_3025_: usize = 0;
    let mut v___x_3026_: usize = 0;
    let mut v_j_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: usize = 0;
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3019_) == 0 {
                    v_es_3022_ = lean_ctor_get(v_x_3019_, 0);
                    v___x_3023_ = lean_box(2);
                    v___x_3024_ = 5usize;
                    v___x_3025_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_3026_ = lean_usize_land(v_x_3020_, v___x_3025_);
                    v_j_3027_ = lean_usize_to_nat(v___x_3026_);
                    v___x_3028_ = lean_array_get_borrowed(v___x_3023_, v_es_3022_, v_j_3027_);
                    lean_dec(v_j_3027_);
                    match lean_obj_tag(v___x_3028_) {
                        0 => {
                            v_key_3029_ = lean_ctor_get(v___x_3028_, 0);
                            v_val_3030_ = lean_ctor_get(v___x_3028_, 1);
                            v___x_3031_ = lean_name_eq(v_x_3021_, v_key_3029_);
                            if v___x_3031_ == 0 {
                                v___x_3032_ = lean_box(0);
                                return v___x_3032_;
                            } else {
                                lean_inc(v_val_3030_);
                                v___x_3033_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3033_, 0, v_val_3030_);
                                return v___x_3033_;
                            }
                        }
                        1 => {
                            v_node_3034_ = lean_ctor_get(v___x_3028_, 0);
                            v___x_3035_ = lean_usize_shift_right(v_x_3020_, v___x_3024_);
                            v_x_3019_ = v_node_3034_;
                            v_x_3020_ = v___x_3035_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3037_ = lean_box(0);
                            return v___x_3037_;
                        }
                    }
                } else {
                    v_ks_3038_ = lean_ctor_get(v_x_3019_, 0);
                    v_vs_3039_ = lean_ctor_get(v_x_3019_, 1);
                    v___x_3040_ = lean_unsigned_to_nat(0);
                    v___x_3041_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_3038_, v_vs_3039_, v___x_3040_, v_x_3021_);
                    return v___x_3041_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_3042_: *mut LeanObject,
    mut v_x_3043_: *mut LeanObject,
    mut v_x_3044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_324__boxed_3045_: usize = 0;
    let mut v_res_3046_: *mut LeanObject = core::ptr::null_mut();
    v_x_324__boxed_3045_ = lean_unbox_usize(v_x_3043_);
    lean_dec(v_x_3043_);
    v_res_3046_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1___redArg(v_x_3042_, v_x_324__boxed_3045_, v_x_3044_);
    lean_dec(v_x_3044_);
    lean_dec_ref(v_x_3042_);
    return v_res_3046_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0___redArg(
    mut v_x_3047_: *mut LeanObject,
    mut v_x_3048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3050_: u64 = 0;
    let mut v___x_3051_: usize = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: u64 = 0;
    let mut v_hash_3054_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3048_) == 0 {
                    v___x_3053_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_ClassState_addEntry_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
                    v___y_3050_ = v___x_3053_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3054_ = lean_ctor_get_uint64(
                        v_x_3048_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3050_ = v_hash_3054_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3051_ = lean_uint64_to_usize(v___y_3050_);
                v___x_3052_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1___redArg(v_x_3047_, v___x_3051_, v_x_3048_);
                return v___x_3052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_3055_: *mut LeanObject,
    mut v_x_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3057_: *mut LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0___redArg(v_x_3055_, v_x_3056_);
    lean_dec(v_x_3056_);
    lean_dec_ref(v_x_3055_);
    return v_res_3057_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0___redArg(
    mut v_x_3058_: *mut LeanObject,
    mut v_x_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_3060_: u8 = 0;
    v_stage_u2081_3060_ = lean_ctor_get_uint8(
        v_x_3058_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_3060_ == 0 {
        let mut v_map_u2081_3061_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_3062_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_3061_ = lean_ctor_get(v_x_3058_, 0);
        v_map_u2082_3062_ = lean_ctor_get(v_x_3058_, 1);
        v___x_3063_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0___redArg(v_map_u2082_3062_, v_x_3059_);
        if lean_obj_tag(v___x_3063_) == 0 {
            let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
            v___x_3064_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1___redArg(v_map_u2081_3061_, v_x_3059_);
            return v___x_3064_;
        } else {
            return v___x_3063_;
        }
    } else {
        let mut v_map_u2081_3065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_3065_ = lean_ctor_get(v_x_3058_, 0);
        v___x_3066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1___redArg(v_map_u2081_3065_, v_x_3059_);
        return v___x_3066_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0___redArg___boxed(
    mut v_x_3067_: *mut LeanObject,
    mut v_x_3068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3069_: *mut LeanObject = core::ptr::null_mut();
    v_res_3069_ = l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0___redArg(
        v_x_3067_, v_x_3068_,
    );
    lean_dec(v_x_3068_);
    lean_dec_ref(v_x_3067_);
    return v_res_3069_;
}
pub unsafe fn l_Lean_getOutParamPositions_x3f(
    mut v_env_3070_: *mut LeanObject,
    mut v_declName_3071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outParamMap_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    v___x_3072_ = l_Lean_classExtension;
    v_toEnvExtension_3073_ = lean_ctor_get(v___x_3072_, 0);
    v_asyncMode_3074_ = lean_ctor_get(v_toEnvExtension_3073_, 2);
    v___x_3075_ = l_Lean_instInhabitedClassState_default;
    v___x_3076_ = lean_box(0);
    v___x_3077_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_3075_,
        v___x_3072_,
        v_env_3070_,
        v_asyncMode_3074_,
        v___x_3076_,
    );
    v_outParamMap_3078_ = lean_ctor_get(v___x_3077_, 0);
    lean_inc_ref(v_outParamMap_3078_);
    lean_dec(v___x_3077_);
    v___x_3079_ = l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0___redArg(
        v_outParamMap_3078_,
        v_declName_3071_,
    );
    lean_dec_ref(v_outParamMap_3078_);
    return v___x_3079_;
}
pub unsafe fn l_Lean_getOutParamPositions_x3f___boxed(
    mut v_env_3080_: *mut LeanObject,
    mut v_declName_3081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3082_: *mut LeanObject = core::ptr::null_mut();
    v_res_3082_ = l_Lean_getOutParamPositions_x3f(v_env_3080_, v_declName_3081_);
    lean_dec(v_declName_3081_);
    return v_res_3082_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0(
    mut v_00_u03b2_3083_: *mut LeanObject,
    mut v_x_3084_: *mut LeanObject,
    mut v_x_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    v___x_3086_ = l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0___redArg(
        v_x_3084_, v_x_3085_,
    );
    return v___x_3086_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0___boxed(
    mut v_00_u03b2_3087_: *mut LeanObject,
    mut v_x_3088_: *mut LeanObject,
    mut v_x_3089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3090_: *mut LeanObject = core::ptr::null_mut();
    v_res_3090_ = l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0(
        v_00_u03b2_3087_,
        v_x_3088_,
        v_x_3089_,
    );
    lean_dec(v_x_3089_);
    lean_dec_ref(v_x_3088_);
    return v_res_3090_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0(
    mut v_00_u03b2_3091_: *mut LeanObject,
    mut v_x_3092_: *mut LeanObject,
    mut v_x_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    v___x_3094_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0___redArg(v_x_3092_, v_x_3093_);
    return v___x_3094_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_3095_: *mut LeanObject,
    mut v_x_3096_: *mut LeanObject,
    mut v_x_3097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3098_: *mut LeanObject = core::ptr::null_mut();
    v_res_3098_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0(v_00_u03b2_3095_, v_x_3096_, v_x_3097_);
    lean_dec(v_x_3097_);
    lean_dec_ref(v_x_3096_);
    return v_res_3098_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1(
    mut v_00_u03b2_3099_: *mut LeanObject,
    mut v_m_3100_: *mut LeanObject,
    mut v_a_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    v___x_3102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1___redArg(v_m_3100_, v_a_3101_);
    return v___x_3102_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1___boxed(
    mut v_00_u03b2_3103_: *mut LeanObject,
    mut v_m_3104_: *mut LeanObject,
    mut v_a_3105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3106_: *mut LeanObject = core::ptr::null_mut();
    v_res_3106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1(v_00_u03b2_3103_, v_m_3104_, v_a_3105_);
    lean_dec(v_a_3105_);
    lean_dec_ref(v_m_3104_);
    return v_res_3106_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3107_: *mut LeanObject,
    mut v_x_3108_: *mut LeanObject,
    mut v_x_3109_: usize,
    mut v_x_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    v___x_3111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1___redArg(v_x_3108_, v_x_3109_, v_x_3110_);
    return v___x_3111_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3112_: *mut LeanObject,
    mut v_x_3113_: *mut LeanObject,
    mut v_x_3114_: *mut LeanObject,
    mut v_x_3115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_441__boxed_3116_: usize = 0;
    let mut v_res_3117_: *mut LeanObject = core::ptr::null_mut();
    v_x_441__boxed_3116_ = lean_unbox_usize(v_x_3114_);
    lean_dec(v_x_3114_);
    v_res_3117_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1(v_00_u03b2_3112_, v_x_3113_, v_x_441__boxed_3116_, v_x_3115_);
    lean_dec(v_x_3115_);
    lean_dec_ref(v_x_3113_);
    return v_res_3117_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3118_: *mut LeanObject,
    mut v_a_3119_: *mut LeanObject,
    mut v_x_3120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    v___x_3121_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3___redArg(v_a_3119_, v_x_3120_);
    return v___x_3121_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3122_: *mut LeanObject,
    mut v_a_3123_: *mut LeanObject,
    mut v_x_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3125_: *mut LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__1_spec__3(v_00_u03b2_3122_, v_a_3123_, v_x_3124_);
    lean_dec(v_x_3124_);
    lean_dec(v_a_3123_);
    return v_res_3125_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3126_: *mut LeanObject,
    mut v_keys_3127_: *mut LeanObject,
    mut v_vals_3128_: *mut LeanObject,
    mut v_heq_3129_: *mut LeanObject,
    mut v_i_3130_: *mut LeanObject,
    mut v_k_3131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_3127_, v_vals_3128_, v_i_3130_, v_k_3131_);
    return v___x_3132_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_3133_: *mut LeanObject,
    mut v_keys_3134_: *mut LeanObject,
    mut v_vals_3135_: *mut LeanObject,
    mut v_heq_3136_: *mut LeanObject,
    mut v_i_3137_: *mut LeanObject,
    mut v_k_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3139_: *mut LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_3133_, v_keys_3134_, v_vals_3135_, v_heq_3136_, v_i_3137_, v_k_3138_);
    lean_dec(v_k_3138_);
    lean_dec_ref(v_vals_3135_);
    lean_dec_ref(v_keys_3134_);
    return v_res_3139_;
}
pub unsafe fn lean_has_out_params(
    mut v_env_3140_: *mut LeanObject,
    mut v_declName_3141_: *mut LeanObject,
) -> u8 {
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    v___x_3142_ = l_Lean_getOutParamPositions_x3f(v_env_3140_, v_declName_3141_);
    lean_dec(v_declName_3141_);
    if lean_obj_tag(v___x_3142_) == 0 {
        let mut v___x_3143_: u8 = 0;
        v___x_3143_ = 0;
        return v___x_3143_;
    } else {
        let mut v_val_3144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3147_: u8 = 0;
        v_val_3144_ = lean_ctor_get(v___x_3142_, 0);
        lean_inc(v_val_3144_);
        lean_dec_ref_known(v___x_3142_, 1);
        v___x_3145_ = lean_array_get_size(v_val_3144_);
        lean_dec(v_val_3144_);
        v___x_3146_ = lean_unsigned_to_nat(0);
        v___x_3147_ = lean_nat_dec_eq(v___x_3145_, v___x_3146_);
        if v___x_3147_ == 0 {
            let mut v___x_3148_: u8 = 0;
            v___x_3148_ = 1;
            return v___x_3148_;
        } else {
            let mut v___x_3149_: u8 = 0;
            v___x_3149_ = 0;
            return v___x_3149_;
        }
    }
}
pub unsafe fn l_Lean_hasOutParams___boxed(
    mut v_env_3150_: *mut LeanObject,
    mut v_declName_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: u8 = 0;
    let mut v_r_3153_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = lean_has_out_params(v_env_3150_, v_declName_3151_);
    v_r_3153_ = lean_box((v_res_3152_) as usize);
    return v_r_3153_;
}
pub unsafe fn l_Lean_getOutLevelParamPositions_x3f(
    mut v_env_3154_: *mut LeanObject,
    mut v_declName_3155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outLevelParamMap_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_classExtension;
    v_toEnvExtension_3157_ = lean_ctor_get(v___x_3156_, 0);
    v_asyncMode_3158_ = lean_ctor_get(v_toEnvExtension_3157_, 2);
    v___x_3159_ = l_Lean_instInhabitedClassState_default;
    v___x_3160_ = lean_box(0);
    v___x_3161_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_3159_,
        v___x_3156_,
        v_env_3154_,
        v_asyncMode_3158_,
        v___x_3160_,
    );
    v_outLevelParamMap_3162_ = lean_ctor_get(v___x_3161_, 1);
    lean_inc_ref(v_outLevelParamMap_3162_);
    lean_dec(v___x_3161_);
    v___x_3163_ = l_Lean_SMap_find_x3f___at___00Lean_getOutParamPositions_x3f_spec__0___redArg(
        v_outLevelParamMap_3162_,
        v_declName_3155_,
    );
    lean_dec_ref(v_outLevelParamMap_3162_);
    return v___x_3163_;
}
pub unsafe fn l_Lean_getOutLevelParamPositions_x3f___boxed(
    mut v_env_3164_: *mut LeanObject,
    mut v_declName_3165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3166_: *mut LeanObject = core::ptr::null_mut();
    v_res_3166_ = l_Lean_getOutLevelParamPositions_x3f(v_env_3164_, v_declName_3165_);
    lean_dec(v_declName_3165_);
    return v_res_3166_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0_spec__0(
    mut v_a_3167_: *mut LeanObject,
    mut v_as_3168_: *mut LeanObject,
    mut v_i_3169_: usize,
    mut v_stop_3170_: usize,
) -> u8 {
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: usize = 0;
    let mut v___x_3177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3171_ = lean_usize_dec_eq(v_i_3169_, v_stop_3170_);
                if v___x_3171_ == 0 {
                    v___x_3172_ = lean_array_uget_borrowed(v_as_3168_, v_i_3169_);
                    v___x_3173_ = l_Lean_instBEqFVarId_beq(v_a_3167_, v___x_3172_);
                    if v___x_3173_ == 0 {
                        v___x_3174_ = 1usize;
                        v___x_3175_ = lean_usize_add(v_i_3169_, v___x_3174_);
                        v_i_3169_ = v___x_3175_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3173_;
                    }
                } else {
                    v___x_3177_ = 0;
                    return v___x_3177_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0_spec__0___boxed(
    mut v_a_3178_: *mut LeanObject,
    mut v_as_3179_: *mut LeanObject,
    mut v_i_3180_: *mut LeanObject,
    mut v_stop_3181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3182_: usize = 0;
    let mut v_stop_boxed_3183_: usize = 0;
    let mut v_res_3184_: u8 = 0;
    let mut v_r_3185_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3182_ = lean_unbox_usize(v_i_3180_);
    lean_dec(v_i_3180_);
    v_stop_boxed_3183_ = lean_unbox_usize(v_stop_3181_);
    lean_dec(v_stop_3181_);
    v_res_3184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0_spec__0(v_a_3178_, v_as_3179_, v_i_boxed_3182_, v_stop_boxed_3183_);
    lean_dec_ref(v_as_3179_);
    lean_dec(v_a_3178_);
    v_r_3185_ = lean_box((v_res_3184_) as usize);
    return v_r_3185_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0(
    mut v_as_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
) -> u8 {
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: u8 = 0;
    v___x_3188_ = lean_unsigned_to_nat(0);
    v___x_3189_ = lean_array_get_size(v_as_3186_);
    v___x_3190_ = lean_nat_dec_lt(v___x_3188_, v___x_3189_);
    if v___x_3190_ == 0 {
        return v___x_3190_;
    } else {
        if v___x_3190_ == 0 {
            return v___x_3190_;
        } else {
            let mut v___x_3191_: usize = 0;
            let mut v___x_3192_: usize = 0;
            let mut v___x_3193_: u8 = 0;
            v___x_3191_ = 0usize;
            v___x_3192_ = lean_usize_of_nat(v___x_3189_);
            v___x_3193_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0_spec__0(v_a_3187_, v_as_3186_, v___x_3191_, v___x_3192_);
            return v___x_3193_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0___boxed(
    mut v_as_3194_: *mut LeanObject,
    mut v_a_3195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3196_: u8 = 0;
    let mut v_r_3197_: *mut LeanObject = core::ptr::null_mut();
    v_res_3196_ = l_Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0(
        v_as_3194_, v_a_3195_,
    );
    lean_dec(v_a_3195_);
    lean_dec_ref(v_as_3194_);
    v_r_3197_ = lean_box((v_res_3196_) as usize);
    return v_r_3197_;
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(
    mut v_outParamFVarIds_3198_: *mut LeanObject,
    mut v_e_3199_: *mut LeanObject,
) -> u8 {
    let mut v___x_3200_: u8 = 0;
    let mut v_d_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v_binderType_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: u8 = 0;
    let mut v_fn_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: u8 = 0;
    let mut v_struct_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: u8 = 0;
    let mut v___x_3226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3200_ = l_Lean_Expr_hasFVar(v_e_3199_);
                if v___x_3200_ == 0 {
                    return v___x_3200_;
                } else {
                    match lean_obj_tag(v_e_3199_) {
                        7 => {
                            v_binderType_3206_ = lean_ctor_get(v_e_3199_, 1);
                            v_body_3207_ = lean_ctor_get(v_e_3199_, 2);
                            v_d_3202_ = v_binderType_3206_;
                            v_b_3203_ = v_body_3207_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_binderType_3208_ = lean_ctor_get(v_e_3199_, 1);
                            v_body_3209_ = lean_ctor_get(v_e_3199_, 2);
                            v_d_3202_ = v_binderType_3208_;
                            v_b_3203_ = v_body_3209_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_3210_ = lean_ctor_get(v_e_3199_, 1);
                            v_e_3199_ = v_expr_3210_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_3212_ = lean_ctor_get(v_e_3199_, 1);
                            v_value_3213_ = lean_ctor_get(v_e_3199_, 2);
                            v_body_3214_ = lean_ctor_get(v_e_3199_, 3);
                            v___x_3215_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(v_outParamFVarIds_3198_, v_type_3212_);
                            if v___x_3215_ == 0 {
                                v___x_3216_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(v_outParamFVarIds_3198_, v_value_3213_);
                                if v___x_3216_ == 0 {
                                    v_e_3199_ = v_body_3214_;
                                    state = 0;
                                    continue;
                                } else {
                                    return v___x_3200_;
                                }
                            } else {
                                return v___x_3200_;
                            }
                        }
                        5 => {
                            v_fn_3218_ = lean_ctor_get(v_e_3199_, 0);
                            v_arg_3219_ = lean_ctor_get(v_e_3199_, 1);
                            v___x_3220_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(v_outParamFVarIds_3198_, v_fn_3218_);
                            if v___x_3220_ == 0 {
                                v_e_3199_ = v_arg_3219_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_3200_;
                            }
                        }
                        11 => {
                            v_struct_3222_ = lean_ctor_get(v_e_3199_, 2);
                            v_e_3199_ = v_struct_3222_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v_fvarId_3224_ = lean_ctor_get(v_e_3199_, 0);
                            v___x_3225_ = l_Array_contains___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__0(v_outParamFVarIds_3198_, v_fvarId_3224_);
                            return v___x_3225_;
                        }
                        _ => {
                            v___x_3226_ = 0;
                            return v___x_3226_;
                        }
                    }
                }
            }
            1 => {
                v___x_3204_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(v_outParamFVarIds_3198_, v_d_3202_);
                if v___x_3204_ == 0 {
                    v_e_3199_ = v_b_3203_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3200_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1___boxed(
    mut v_outParamFVarIds_3227_: *mut LeanObject,
    mut v_e_3228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3229_: u8 = 0;
    let mut v_r_3230_: *mut LeanObject = core::ptr::null_mut();
    v_res_3229_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(v_outParamFVarIds_3227_, v_e_3228_);
    lean_dec_ref(v_e_3228_);
    lean_dec_ref(v_outParamFVarIds_3227_);
    v_r_3230_ = lean_box((v_res_3229_) as usize);
    return v_r_3230_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_checkOutParam___closed__3() -> *mut LeanObject {
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    v___x_3235_ = l___private_Lean_Class_0__Lean_checkOutParam___closed__2;
    v___x_3236_ = l_Lean_stringToMessageData(v___x_3235_);
    return v___x_3236_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_checkOutParam___closed__5() -> *mut LeanObject {
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    v___x_3238_ = l___private_Lean_Class_0__Lean_checkOutParam___closed__4;
    v___x_3239_ = l_Lean_stringToMessageData(v___x_3238_);
    return v___x_3239_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_checkOutParam(
    mut v_i_3240_: *mut LeanObject,
    mut v_outParamFVarIds_3241_: *mut LeanObject,
    mut v_outParams_3242_: *mut LeanObject,
    mut v_type_3243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderType_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3246_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvar_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: u8 = 0;
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_type_3243_) == 7 {
                    v_binderType_3244_ = lean_ctor_get(v_type_3243_, 1);
                    lean_inc_ref_n(v_binderType_3244_, 2);
                    v_body_3245_ = lean_ctor_get(v_type_3243_, 2);
                    lean_inc_ref(v_body_3245_);
                    v_binderInfo_3246_ = lean_ctor_get_uint8(
                        v_type_3243_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_dec_ref_known(v_type_3243_, 3);
                    v___x_3258_ = lean_is_out_param(v_binderType_3244_);
                    if v___x_3258_ == 0 {
                        v___x_3259_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(v_outParamFVarIds_3241_, v_binderType_3244_);
                        lean_dec_ref(v_binderType_3244_);
                        if v___x_3259_ == 0 {
                            v___x_3260_ = lean_unsigned_to_nat(1);
                            v___x_3261_ = lean_nat_add(v_i_3240_, v___x_3260_);
                            lean_dec(v_i_3240_);
                            v_i_3240_ = v___x_3261_;
                            v_type_3243_ = v_body_3245_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3263_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3246_);
                            if v___x_3263_ == 0 {
                                lean_dec_ref(v_body_3245_);
                                lean_dec_ref(v_outParams_3242_);
                                lean_dec_ref(v_outParamFVarIds_3241_);
                                v___x_3264_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_checkOutParam___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_checkOutParam___closed__3_once), _init_l___private_Lean_Class_0__Lean_checkOutParam___closed__3);
                                v___x_3265_ = lean_unsigned_to_nat(1);
                                v___x_3266_ = lean_nat_add(v_i_3240_, v___x_3265_);
                                lean_dec(v_i_3240_);
                                v___x_3267_ = l_Nat_reprFast(v___x_3266_);
                                v___x_3268_ = lean_alloc_ctor(3, 1, (0) as u32);
                                lean_ctor_set(v___x_3268_, 0, v___x_3267_);
                                v___x_3269_ = l_Lean_MessageData_ofFormat(v___x_3268_);
                                v___x_3270_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3270_, 0, v___x_3264_);
                                lean_ctor_set(v___x_3270_, 1, v___x_3269_);
                                v___x_3271_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_checkOutParam___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_checkOutParam___closed__5_once), _init_l___private_Lean_Class_0__Lean_checkOutParam___closed__5);
                                v___x_3272_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3272_, 0, v___x_3270_);
                                lean_ctor_set(v___x_3272_, 1, v___x_3271_);
                                v___x_3273_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3273_, 0, v___x_3272_);
                                return v___x_3273_;
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_binderType_3244_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_3243_);
                    lean_dec_ref(v_outParamFVarIds_3241_);
                    lean_dec(v_i_3240_);
                    v___x_3274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3274_, 0, v_outParams_3242_);
                    return v___x_3274_;
                }
            }
            1 => {
                v___x_3248_ = l___private_Lean_Class_0__Lean_checkOutParam___closed__1;
                v___x_3249_ = lean_array_get_size(v_outParamFVarIds_3241_);
                v_fvarId_3250_ = l_Lean_Name_num___override(v___x_3248_, v___x_3249_);
                lean_inc(v_fvarId_3250_);
                v_fvar_3251_ = l_Lean_mkFVar(v_fvarId_3250_);
                v_b_3252_ = lean_expr_instantiate1(v_body_3245_, v_fvar_3251_);
                lean_dec_ref(v_fvar_3251_);
                lean_dec_ref(v_body_3245_);
                v___x_3253_ = lean_unsigned_to_nat(1);
                v___x_3254_ = lean_nat_add(v_i_3240_, v___x_3253_);
                v___x_3255_ = lean_array_push(v_outParamFVarIds_3241_, v_fvarId_3250_);
                v___x_3256_ = lean_array_push(v_outParams_3242_, v_i_3240_);
                v_i_3240_ = v___x_3254_;
                v_outParamFVarIds_3241_ = v___x_3255_;
                v_outParams_3242_ = v___x_3256_;
                v_type_3243_ = v_b_3252_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go_spec__0(
    mut v_msg_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    v___x_3276_ = l_Lean_instInhabitedExpr;
    v___x_3277_ = lean_panic_fn_borrowed(v___x_3276_, v_msg_3275_);
    return v___x_3277_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__3()
-> *mut LeanObject {
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    v___x_3281_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__2;
    v___x_3282_ = lean_unsigned_to_nat(24);
    v___x_3283_ = lean_unsigned_to_nat(1913);
    v___x_3284_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__1;
    v___x_3285_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__0;
    v___x_3286_ = l_mkPanicMessageWithDecl(
        v___x_3285_,
        v___x_3284_,
        v___x_3283_,
        v___x_3282_,
        v___x_3281_,
    );
    return v___x_3286_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__5()
-> *mut LeanObject {
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    v___x_3288_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__2;
    v___x_3289_ = lean_unsigned_to_nat(23);
    v___x_3290_ = lean_unsigned_to_nat(1902);
    v___x_3291_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__4;
    v___x_3292_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__0;
    v___x_3293_ = l_mkPanicMessageWithDecl(
        v___x_3292_,
        v___x_3291_,
        v___x_3290_,
        v___x_3289_,
        v___x_3288_,
    );
    return v___x_3293_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go(
    mut v_type_3294_: *mut LeanObject,
    mut v_typeAux_3295_: *mut LeanObject,
    mut v_outParamFVarIds_3296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3298_: u8 = 0;
    let mut v___y_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3302_: u8 = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3307_: u8 = 0;
    let mut v___y_3308_: u8 = 0;
    let mut v___y_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3312_: u8 = 0;
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3318_: u8 = 0;
    let mut v_binderName_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3323_: u8 = 0;
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bNew_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: usize = 0;
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: usize = 0;
    let mut v___x_3331_: usize = 0;
    let mut v___x_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dNew_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3340_: u8 = 0;
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvar_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bNew_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: u8 = 0;
    let mut v___x_3350_: usize = 0;
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: usize = 0;
    let mut v___x_3354_: usize = 0;
    let mut v___x_3355_: u8 = 0;
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_typeAux_3295_) == 7 {
                    v_binderType_3316_ = lean_ctor_get(v_typeAux_3295_, 1);
                    lean_inc_ref_n(v_binderType_3316_, 2);
                    v_body_3317_ = lean_ctor_get(v_typeAux_3295_, 2);
                    lean_inc_ref(v_body_3317_);
                    v_binderInfo_3318_ = lean_ctor_get_uint8(
                        v_typeAux_3295_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_dec_ref_known(v_typeAux_3295_, 3);
                    v___x_3358_ = lean_is_out_param(v_binderType_3316_);
                    if v___x_3358_ == 0 {
                        v___x_3359_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Class_0__Lean_checkOutParam_spec__1(v_outParamFVarIds_3296_, v_binderType_3316_);
                        lean_dec_ref(v_binderType_3316_);
                        if v___x_3359_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            v___x_3360_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3318_);
                            if v___x_3360_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                v___x_3361_ = l_Lean_Expr_bindingDomain_x21(v_type_3294_);
                                v_dNew_3336_ = v___x_3361_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_binderType_3316_);
                        v___x_3362_ = l_Lean_Expr_bindingDomain_x21(v_type_3294_);
                        v___x_3363_ = l_Lean_Expr_appArg_x21(v___x_3362_);
                        lean_dec_ref(v___x_3362_);
                        v_dNew_3336_ = v___x_3363_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_outParamFVarIds_3296_);
                    lean_dec_ref(v_typeAux_3295_);
                    return v_type_3294_;
                }
            }
            1 => {
                if v___y_3302_ == 0 {
                    lean_dec_ref(v_type_3294_);
                    v___x_3303_ = l_Lean_Expr_forallE___override(
                        v___y_3301_,
                        v___y_3299_,
                        v___y_3300_,
                        v___y_3298_,
                    );
                    return v___x_3303_;
                } else {
                    v___x_3304_ = l_Lean_instBEqBinderInfo_beq(v___y_3298_, v___y_3298_);
                    if v___x_3304_ == 0 {
                        lean_dec_ref(v_type_3294_);
                        v___x_3305_ = l_Lean_Expr_forallE___override(
                            v___y_3301_,
                            v___y_3299_,
                            v___y_3300_,
                            v___y_3298_,
                        );
                        return v___x_3305_;
                    } else {
                        lean_dec(v___y_3301_);
                        lean_dec_ref(v___y_3300_);
                        lean_dec_ref(v___y_3299_);
                        return v_type_3294_;
                    }
                }
            }
            2 => {
                if v___y_3312_ == 0 {
                    lean_dec_ref(v_type_3294_);
                    v___x_3313_ = l_Lean_Expr_forallE___override(
                        v___y_3311_,
                        v___y_3309_,
                        v___y_3310_,
                        v___y_3308_,
                    );
                    return v___x_3313_;
                } else {
                    v___x_3314_ = l_Lean_instBEqBinderInfo_beq(v___y_3307_, v___y_3308_);
                    if v___x_3314_ == 0 {
                        lean_dec_ref(v_type_3294_);
                        v___x_3315_ = l_Lean_Expr_forallE___override(
                            v___y_3311_,
                            v___y_3309_,
                            v___y_3310_,
                            v___y_3308_,
                        );
                        return v___x_3315_;
                    } else {
                        lean_dec(v___y_3311_);
                        lean_dec_ref(v___y_3310_);
                        lean_dec_ref(v___y_3309_);
                        return v_type_3294_;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_type_3294_) == 7 {
                    v_binderName_3320_ = lean_ctor_get(v_type_3294_, 0);
                    v_binderType_3321_ = lean_ctor_get(v_type_3294_, 1);
                    v_body_3322_ = lean_ctor_get(v_type_3294_, 2);
                    v_binderInfo_3323_ = lean_ctor_get_uint8(
                        v_type_3294_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3324_ = l_Lean_Expr_bindingBody_x21(v_type_3294_);
                    v_bNew_3325_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go(
                        v___x_3324_,
                        v_body_3317_,
                        v_outParamFVarIds_3296_,
                    );
                    v___x_3326_ = l_Lean_Expr_bindingDomain_x21(v_type_3294_);
                    v___x_3327_ = lean_ptr_addr(v_binderType_3321_);
                    v___x_3328_ = lean_ptr_addr(v___x_3326_);
                    v___x_3329_ = lean_usize_dec_eq(v___x_3327_, v___x_3328_);
                    if v___x_3329_ == 0 {
                        lean_inc(v_binderName_3320_);
                        v___y_3298_ = v_binderInfo_3323_;
                        v___y_3299_ = v___x_3326_;
                        v___y_3300_ = v_bNew_3325_;
                        v___y_3301_ = v_binderName_3320_;
                        v___y_3302_ = v___x_3329_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3330_ = lean_ptr_addr(v_body_3322_);
                        v___x_3331_ = lean_ptr_addr(v_bNew_3325_);
                        v___x_3332_ = lean_usize_dec_eq(v___x_3330_, v___x_3331_);
                        lean_inc(v_binderName_3320_);
                        v___y_3298_ = v_binderInfo_3323_;
                        v___y_3299_ = v___x_3326_;
                        v___y_3300_ = v_bNew_3325_;
                        v___y_3301_ = v_binderName_3320_;
                        v___y_3302_ = v___x_3332_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_body_3317_);
                    lean_dec_ref(v_outParamFVarIds_3296_);
                    lean_dec_ref(v_type_3294_);
                    v___x_3333_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__3_once), _init_l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__3);
                    v___x_3334_ = l_panic___at___00__private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go_spec__0(v___x_3333_);
                    return v___x_3334_;
                }
            }
            4 => {
                if lean_obj_tag(v_type_3294_) == 7 {
                    v_binderName_3337_ = lean_ctor_get(v_type_3294_, 0);
                    v_binderType_3338_ = lean_ctor_get(v_type_3294_, 1);
                    v_body_3339_ = lean_ctor_get(v_type_3294_, 2);
                    v_binderInfo_3340_ = lean_ctor_get_uint8(
                        v_type_3294_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3341_ = l___private_Lean_Class_0__Lean_checkOutParam___closed__1;
                    v___x_3342_ = lean_array_get_size(v_outParamFVarIds_3296_);
                    v_fvarId_3343_ = l_Lean_Name_num___override(v___x_3341_, v___x_3342_);
                    lean_inc(v_fvarId_3343_);
                    v_fvar_3344_ = l_Lean_mkFVar(v_fvarId_3343_);
                    v_b_3345_ = lean_expr_instantiate1(v_body_3317_, v_fvar_3344_);
                    lean_dec_ref(v_fvar_3344_);
                    lean_dec_ref(v_body_3317_);
                    v___x_3346_ = l_Lean_Expr_bindingBody_x21(v_type_3294_);
                    v___x_3347_ = lean_array_push(v_outParamFVarIds_3296_, v_fvarId_3343_);
                    v_bNew_3348_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go(
                        v___x_3346_,
                        v_b_3345_,
                        v___x_3347_,
                    );
                    v___x_3349_ = 1;
                    v___x_3350_ = lean_ptr_addr(v_binderType_3338_);
                    v___x_3351_ = lean_ptr_addr(v_dNew_3336_);
                    v___x_3352_ = lean_usize_dec_eq(v___x_3350_, v___x_3351_);
                    if v___x_3352_ == 0 {
                        lean_inc(v_binderName_3337_);
                        v___y_3307_ = v_binderInfo_3340_;
                        v___y_3308_ = v___x_3349_;
                        v___y_3309_ = v_dNew_3336_;
                        v___y_3310_ = v_bNew_3348_;
                        v___y_3311_ = v_binderName_3337_;
                        v___y_3312_ = v___x_3352_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3353_ = lean_ptr_addr(v_body_3339_);
                        v___x_3354_ = lean_ptr_addr(v_bNew_3348_);
                        v___x_3355_ = lean_usize_dec_eq(v___x_3353_, v___x_3354_);
                        lean_inc(v_binderName_3337_);
                        v___y_3307_ = v_binderInfo_3340_;
                        v___y_3308_ = v___x_3349_;
                        v___y_3309_ = v_dNew_3336_;
                        v___y_3310_ = v_bNew_3348_;
                        v___y_3311_ = v_binderName_3337_;
                        v___y_3312_ = v___x_3355_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_dNew_3336_);
                    lean_dec_ref(v_body_3317_);
                    lean_dec_ref(v_outParamFVarIds_3296_);
                    lean_dec_ref(v_type_3294_);
                    v___x_3356_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__5_once), _init_l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go___closed__5);
                    v___x_3357_ = l_panic___at___00__private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go_spec__0(v___x_3356_);
                    return v___x_3357_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_mk_outparam_args_implicit(mut v_type_3366_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    v___x_3367_ = l_Lean_mkOutParamArgsImplicit___closed__0;
    lean_inc_ref(v_type_3366_);
    v___x_3368_ = l___private_Lean_Class_0__Lean_mkOutParamArgsImplicit_go(
        v_type_3366_,
        v_type_3366_,
        v___x_3367_,
    );
    return v___x_3368_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0_spec__0(
    mut v_a_3369_: *mut LeanObject,
    mut v_as_3370_: *mut LeanObject,
    mut v_i_3371_: usize,
    mut v_stop_3372_: usize,
) -> u8 {
    let mut v___x_3373_: u8 = 0;
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: usize = 0;
    let mut v___x_3377_: usize = 0;
    let mut v___x_3379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3373_ = lean_usize_dec_eq(v_i_3371_, v_stop_3372_);
                if v___x_3373_ == 0 {
                    v___x_3374_ = lean_array_uget_borrowed(v_as_3370_, v_i_3371_);
                    v___x_3375_ = lean_nat_dec_eq(v_a_3369_, v___x_3374_);
                    if v___x_3375_ == 0 {
                        v___x_3376_ = 1usize;
                        v___x_3377_ = lean_usize_add(v_i_3371_, v___x_3376_);
                        v_i_3371_ = v___x_3377_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3375_;
                    }
                } else {
                    v___x_3379_ = 0;
                    return v___x_3379_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0_spec__0___boxed(
    mut v_a_3380_: *mut LeanObject,
    mut v_as_3381_: *mut LeanObject,
    mut v_i_3382_: *mut LeanObject,
    mut v_stop_3383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3384_: usize = 0;
    let mut v_stop_boxed_3385_: usize = 0;
    let mut v_res_3386_: u8 = 0;
    let mut v_r_3387_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3384_ = lean_unbox_usize(v_i_3382_);
    lean_dec(v_i_3382_);
    v_stop_boxed_3385_ = lean_unbox_usize(v_stop_3383_);
    lean_dec(v_stop_3383_);
    v_res_3386_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0_spec__0(v_a_3380_, v_as_3381_, v_i_boxed_3384_, v_stop_boxed_3385_);
    lean_dec_ref(v_as_3381_);
    lean_dec(v_a_3380_);
    v_r_3387_ = lean_box((v_res_3386_) as usize);
    return v_r_3387_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0(
    mut v_as_3388_: *mut LeanObject,
    mut v_a_3389_: *mut LeanObject,
) -> u8 {
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    v___x_3390_ = lean_unsigned_to_nat(0);
    v___x_3391_ = lean_array_get_size(v_as_3388_);
    v___x_3392_ = lean_nat_dec_lt(v___x_3390_, v___x_3391_);
    if v___x_3392_ == 0 {
        return v___x_3392_;
    } else {
        if v___x_3392_ == 0 {
            return v___x_3392_;
        } else {
            let mut v___x_3393_: usize = 0;
            let mut v___x_3394_: usize = 0;
            let mut v___x_3395_: u8 = 0;
            v___x_3393_ = 0usize;
            v___x_3394_ = lean_usize_of_nat(v___x_3391_);
            v___x_3395_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0_spec__0(v_a_3389_, v_as_3388_, v___x_3393_, v___x_3394_);
            return v___x_3395_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0___boxed(
    mut v_as_3396_: *mut LeanObject,
    mut v_a_3397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3398_: u8 = 0;
    let mut v_r_3399_: *mut LeanObject = core::ptr::null_mut();
    v_res_3398_ =
        l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0(
            v_as_3396_, v_a_3397_,
        );
    lean_dec(v_a_3397_);
    lean_dec_ref(v_as_3396_);
    v_r_3399_ = lean_box((v_res_3398_) as usize);
    return v_r_3399_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_computeOutLevelParams_go(
    mut v_outParams_3400_: *mut LeanObject,
    mut v_type_3401_: *mut LeanObject,
    mut v_i_3402_: *mut LeanObject,
    mut v_s_3403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderType_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: u8 = 0;
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_type_3401_) == 7 {
                    v_binderType_3404_ = lean_ctor_get(v_type_3401_, 1);
                    lean_inc_ref(v_binderType_3404_);
                    v_body_3405_ = lean_ctor_get(v_type_3401_, 2);
                    lean_inc_ref(v_body_3405_);
                    lean_dec_ref_known(v_type_3401_, 3);
                    v___x_3406_ = l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_go_spec__0(v_outParams_3400_, v_i_3402_);
                    if v___x_3406_ == 0 {
                        v___x_3407_ = lean_unsigned_to_nat(1);
                        v___x_3408_ = lean_nat_add(v_i_3402_, v___x_3407_);
                        lean_dec(v_i_3402_);
                        v___x_3409_ = l_Lean_collectLevelParams(v_s_3403_, v_binderType_3404_);
                        v_type_3401_ = v_body_3405_;
                        v_i_3402_ = v___x_3408_;
                        v_s_3403_ = v___x_3409_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_binderType_3404_);
                        v___x_3411_ = lean_unsigned_to_nat(1);
                        v___x_3412_ = lean_nat_add(v_i_3402_, v___x_3411_);
                        lean_dec(v_i_3402_);
                        v_type_3401_ = v_body_3405_;
                        v_i_3402_ = v___x_3412_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_i_3402_);
                    lean_dec_ref(v_type_3401_);
                    return v_s_3403_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Class_0__Lean_computeOutLevelParams_go___boxed(
    mut v_outParams_3414_: *mut LeanObject,
    mut v_type_3415_: *mut LeanObject,
    mut v_i_3416_: *mut LeanObject,
    mut v_s_3417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3418_: *mut LeanObject = core::ptr::null_mut();
    v_res_3418_ = l___private_Lean_Class_0__Lean_computeOutLevelParams_go(
        v_outParams_3414_,
        v_type_3415_,
        v_i_3416_,
        v_s_3417_,
    );
    lean_dec_ref(v_outParams_3414_);
    return v_res_3418_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0_spec__0(
    mut v_a_3419_: *mut LeanObject,
    mut v_as_3420_: *mut LeanObject,
    mut v_i_3421_: usize,
    mut v_stop_3422_: usize,
) -> u8 {
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: u8 = 0;
    let mut v___x_3426_: usize = 0;
    let mut v___x_3427_: usize = 0;
    let mut v___x_3429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3423_ = lean_usize_dec_eq(v_i_3421_, v_stop_3422_);
                if v___x_3423_ == 0 {
                    v___x_3424_ = lean_array_uget_borrowed(v_as_3420_, v_i_3421_);
                    v___x_3425_ = lean_name_eq(v_a_3419_, v___x_3424_);
                    if v___x_3425_ == 0 {
                        v___x_3426_ = 1usize;
                        v___x_3427_ = lean_usize_add(v_i_3421_, v___x_3426_);
                        v_i_3421_ = v___x_3427_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3425_;
                    }
                } else {
                    v___x_3429_ = 0;
                    return v___x_3429_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0_spec__0___boxed(
    mut v_a_3430_: *mut LeanObject,
    mut v_as_3431_: *mut LeanObject,
    mut v_i_3432_: *mut LeanObject,
    mut v_stop_3433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3434_: usize = 0;
    let mut v_stop_boxed_3435_: usize = 0;
    let mut v_res_3436_: u8 = 0;
    let mut v_r_3437_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3434_ = lean_unbox_usize(v_i_3432_);
    lean_dec(v_i_3432_);
    v_stop_boxed_3435_ = lean_unbox_usize(v_stop_3433_);
    lean_dec(v_stop_3433_);
    v_res_3436_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0_spec__0(v_a_3430_, v_as_3431_, v_i_boxed_3434_, v_stop_boxed_3435_);
    lean_dec_ref(v_as_3431_);
    lean_dec(v_a_3430_);
    v_r_3437_ = lean_box((v_res_3436_) as usize);
    return v_r_3437_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0(
    mut v_as_3438_: *mut LeanObject,
    mut v_a_3439_: *mut LeanObject,
) -> u8 {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    v___x_3440_ = lean_unsigned_to_nat(0);
    v___x_3441_ = lean_array_get_size(v_as_3438_);
    v___x_3442_ = lean_nat_dec_lt(v___x_3440_, v___x_3441_);
    if v___x_3442_ == 0 {
        return v___x_3442_;
    } else {
        if v___x_3442_ == 0 {
            return v___x_3442_;
        } else {
            let mut v___x_3443_: usize = 0;
            let mut v___x_3444_: usize = 0;
            let mut v___x_3445_: u8 = 0;
            v___x_3443_ = 0usize;
            v___x_3444_ = lean_usize_of_nat(v___x_3441_);
            v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0_spec__0(v_a_3439_, v_as_3438_, v___x_3443_, v___x_3444_);
            return v___x_3445_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0___boxed(
    mut v_as_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3448_: u8 = 0;
    let mut v_r_3449_: *mut LeanObject = core::ptr::null_mut();
    v_res_3448_ =
        l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0(
            v_as_3446_, v_a_3447_,
        );
    lean_dec(v_a_3447_);
    lean_dec_ref(v_as_3446_);
    v_r_3449_ = lean_box((v_res_3448_) as usize);
    return v_r_3449_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1___redArg(
    mut v_nonOutLevels_3450_: *mut LeanObject,
    mut v_as_x27_3451_: *mut LeanObject,
    mut v_b_3452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v_result_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3451_) == 0 {
                    return v_b_3452_;
                } else {
                    v_head_3453_ = lean_ctor_get(v_as_x27_3451_, 0);
                    v_tail_3454_ = lean_ctor_get(v_as_x27_3451_, 1);
                    v_fst_3455_ = lean_ctor_get(v_b_3452_, 0);
                    v_snd_3456_ = lean_ctor_get(v_b_3452_, 1);
                    v_isSharedCheck_3470_ = (!lean_is_exclusive(v_b_3452_)) as u8;
                    if v_isSharedCheck_3470_ == 0 {
                        v___x_3458_ = v_b_3452_;
                        v_isShared_3459_ = v_isSharedCheck_3470_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3456_);
                        lean_inc(v_fst_3455_);
                        lean_dec(v_b_3452_);
                        v___x_3458_ = lean_box(0);
                        v_isShared_3459_ = v_isSharedCheck_3470_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3468_ = l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0(v_nonOutLevels_3450_, v_head_3453_);
                if v___x_3468_ == 0 {
                    lean_inc(v_snd_3456_);
                    v___x_3469_ = lean_array_push(v_fst_3455_, v_snd_3456_);
                    v_result_3461_ = v___x_3469_;
                    state = 2;
                    continue;
                } else {
                    v_result_3461_ = v_fst_3455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3462_ = lean_unsigned_to_nat(1);
                v___x_3463_ = lean_nat_add(v_snd_3456_, v___x_3462_);
                lean_dec(v_snd_3456_);
                if v_isShared_3459_ == 0 {
                    lean_ctor_set(v___x_3458_, 1, v___x_3463_);
                    lean_ctor_set(v___x_3458_, 0, v_result_3461_);
                    v___x_3465_ = v___x_3458_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_result_3461_);
                    lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3463_);
                    v___x_3465_ = v_reuseFailAlloc_3467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_as_x27_3451_ = v_tail_3454_;
                v_b_3452_ = v___x_3465_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1___redArg___boxed(
    mut v_nonOutLevels_3471_: *mut LeanObject,
    mut v_as_x27_3472_: *mut LeanObject,
    mut v_b_3473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3474_: *mut LeanObject = core::ptr::null_mut();
    v_res_3474_ = l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1___redArg(v_nonOutLevels_3471_, v_as_x27_3472_, v_b_3473_);
    lean_dec(v_as_x27_3472_);
    lean_dec_ref(v_nonOutLevels_3471_);
    return v_res_3474_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__0()
-> *mut LeanObject {
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    v___x_3475_ = lean_box(0);
    v___x_3476_ = lean_unsigned_to_nat(16);
    v___x_3477_ = lean_mk_array(v___x_3476_, v___x_3475_);
    return v___x_3477_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__1()
-> *mut LeanObject {
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    v___x_3478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__0),
        core::ptr::addr_of_mut!(
            l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__0_once
        ),
        _init_l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__0,
    );
    v_i_3479_ = lean_unsigned_to_nat(0);
    v___x_3480_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3480_, 0, v_i_3479_);
    lean_ctor_set(v___x_3480_, 1, v___x_3478_);
    return v___x_3480_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__2()
-> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ = l_Lean_mkOutParamArgsImplicit___closed__0;
    v___x_3482_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__1_once
        ),
        _init_l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__1,
    );
    v___x_3483_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3483_, 0, v___x_3482_);
    lean_ctor_set(v___x_3483_, 1, v___x_3482_);
    lean_ctor_set(v___x_3483_, 2, v___x_3481_);
    return v___x_3483_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_computeOutLevelParams(
    mut v_type_3487_: *mut LeanObject,
    mut v_outParams_3488_: *mut LeanObject,
    mut v_levelParams_3489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3496_: *mut LeanObject = core::ptr::null_mut();
    v_i_3490_ = lean_unsigned_to_nat(0);
    v___x_3491_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__2),
        core::ptr::addr_of_mut!(
            l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__2_once
        ),
        _init_l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__2,
    );
    v___x_3492_ = l___private_Lean_Class_0__Lean_computeOutLevelParams_go(
        v_outParams_3488_,
        v_type_3487_,
        v_i_3490_,
        v___x_3491_,
    );
    v_params_3493_ = lean_ctor_get(v___x_3492_, 2);
    lean_inc_ref(v_params_3493_);
    lean_dec_ref(v___x_3492_);
    v___x_3494_ = l___private_Lean_Class_0__Lean_computeOutLevelParams___closed__3;
    v___x_3495_ = l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1___redArg(v_params_3493_, v_levelParams_3489_, v___x_3494_);
    lean_dec_ref(v_params_3493_);
    v_fst_3496_ = lean_ctor_get(v___x_3495_, 0);
    lean_inc(v_fst_3496_);
    lean_dec_ref(v___x_3495_);
    return v_fst_3496_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_computeOutLevelParams___boxed(
    mut v_type_3497_: *mut LeanObject,
    mut v_outParams_3498_: *mut LeanObject,
    mut v_levelParams_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_res_3500_ = l___private_Lean_Class_0__Lean_computeOutLevelParams(
        v_type_3497_,
        v_outParams_3498_,
        v_levelParams_3499_,
    );
    lean_dec(v_levelParams_3499_);
    lean_dec_ref(v_outParams_3498_);
    return v_res_3500_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1(
    mut v_nonOutLevels_3501_: *mut LeanObject,
    mut v_as_3502_: *mut LeanObject,
    mut v_as_x27_3503_: *mut LeanObject,
    mut v_b_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v___x_3506_ = l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1___redArg(v_nonOutLevels_3501_, v_as_x27_3503_, v_b_3504_);
    return v___x_3506_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1___boxed(
    mut v_nonOutLevels_3507_: *mut LeanObject,
    mut v_as_3508_: *mut LeanObject,
    mut v_as_x27_3509_: *mut LeanObject,
    mut v_b_3510_: *mut LeanObject,
    mut v_a_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3512_: *mut LeanObject = core::ptr::null_mut();
    v_res_3512_ =
        l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__1(
            v_nonOutLevels_3507_,
            v_as_3508_,
            v_as_x27_3509_,
            v_b_3510_,
            v_a_3511_,
        );
    lean_dec(v_as_x27_3509_);
    lean_dec(v_as_3508_);
    lean_dec_ref(v_nonOutLevels_3507_);
    return v_res_3512_;
}
pub unsafe fn _init_l_Lean_addClass___closed__1() -> *mut LeanObject {
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Lean_addClass___closed__0;
    v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
    return v___x_3515_;
}
pub unsafe fn _init_l_Lean_addClass___closed__3() -> *mut LeanObject {
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    v___x_3517_ = l_Lean_addClass___closed__2;
    v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
    return v___x_3518_;
}
pub unsafe fn _init_l_Lean_addClass___closed__5() -> *mut LeanObject {
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Lean_addClass___closed__4;
    v___x_3521_ = l_Lean_stringToMessageData(v___x_3520_);
    return v___x_3521_;
}
pub unsafe fn _init_l_Lean_addClass___closed__7() -> *mut LeanObject {
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    v___x_3523_ = l_Lean_addClass___closed__6;
    v___x_3524_ = l_Lean_stringToMessageData(v___x_3523_);
    return v___x_3524_;
}
pub unsafe fn _init_l_Lean_addClass___closed__9() -> *mut LeanObject {
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_addClass___closed__8;
    v___x_3527_ = l_Lean_stringToMessageData(v___x_3526_);
    return v___x_3527_;
}
pub unsafe fn l_Lean_addClass(
    mut v_env_3528_: *mut LeanObject,
    mut v_clsName_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3544_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3548_: u8 = 0;
    let mut v_a_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3552_: u8 = 0;
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3573_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_clsName_3529_);
                lean_inc_ref(v_env_3528_);
                v___x_3530_ = lean_is_class(v_env_3528_, v_clsName_3529_);
                if v___x_3530_ == 0 {
                    lean_inc(v_clsName_3529_);
                    lean_inc_ref(v_env_3528_);
                    v___x_3531_ =
                        l_Lean_Environment_find_x3f(v_env_3528_, v_clsName_3529_, v___x_3530_);
                    if lean_obj_tag(v___x_3531_) == 1 {
                        v_val_3532_ = lean_ctor_get(v___x_3531_, 0);
                        v_isSharedCheck_3573_ = (!lean_is_exclusive(v___x_3531_)) as u8;
                        if v_isSharedCheck_3573_ == 0 {
                            v___x_3534_ = v___x_3531_;
                            v_isShared_3535_ = v_isSharedCheck_3573_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_3532_);
                            lean_dec(v___x_3531_);
                            v___x_3534_ = lean_box(0);
                            v_isShared_3535_ = v_isSharedCheck_3573_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3531_);
                        lean_dec_ref(v_env_3528_);
                        v___x_3574_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__5_once),
                            _init_l_Lean_addClass___closed__5,
                        );
                        v___x_3575_ = l_Lean_MessageData_ofName(v_clsName_3529_);
                        v___x_3576_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3576_, 0, v___x_3574_);
                        lean_ctor_set(v___x_3576_, 1, v___x_3575_);
                        v___x_3577_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__7_once),
                            _init_l_Lean_addClass___closed__7,
                        );
                        v___x_3578_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3578_, 0, v___x_3576_);
                        lean_ctor_set(v___x_3578_, 1, v___x_3577_);
                        v___x_3579_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                        return v___x_3579_;
                    }
                } else {
                    lean_dec_ref(v_env_3528_);
                    v___x_3580_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_addClass___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_addClass___closed__9_once),
                        _init_l_Lean_addClass___closed__9,
                    );
                    v___x_3581_ = l_Lean_MessageData_ofConstName(v_clsName_3529_, v___x_3530_);
                    v___x_3582_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3582_, 0, v___x_3580_);
                    lean_ctor_set(v___x_3582_, 1, v___x_3581_);
                    v___x_3583_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_addClass___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_addClass___closed__7_once),
                        _init_l_Lean_addClass___closed__7,
                    );
                    v___x_3584_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3584_, 0, v___x_3582_);
                    lean_ctor_set(v___x_3584_, 1, v___x_3583_);
                    v___x_3585_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3585_, 0, v___x_3584_);
                    return v___x_3585_;
                }
            }
            1 => match lean_obj_tag(v_val_3532_) {
                5 => {
                    lean_del_object(v___x_3534_);
                    state = 2;
                    continue;
                }
                0 => {
                    lean_del_object(v___x_3534_);
                    state = 2;
                    continue;
                }
                _ => {
                    if v___x_3530_ == 0 {
                        lean_dec(v_val_3532_);
                        lean_dec_ref(v_env_3528_);
                        v___x_3565_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__1_once),
                            _init_l_Lean_addClass___closed__1,
                        );
                        v___x_3566_ = l_Lean_MessageData_ofConstName(v_clsName_3529_, v___x_3530_);
                        v___x_3567_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3567_, 0, v___x_3565_);
                        lean_ctor_set(v___x_3567_, 1, v___x_3566_);
                        v___x_3568_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_addClass___closed__3_once),
                            _init_l_Lean_addClass___closed__3,
                        );
                        v___x_3569_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3569_, 0, v___x_3567_);
                        lean_ctor_set(v___x_3569_, 1, v___x_3568_);
                        if v_isShared_3535_ == 0 {
                            lean_ctor_set_tag(v___x_3534_, 0);
                            lean_ctor_set(v___x_3534_, 0, v___x_3569_);
                            v___x_3571_ = v___x_3534_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3569_);
                            v___x_3571_ = v_reuseFailAlloc_3572_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3534_);
                        state = 2;
                        continue;
                    }
                }
            },
            2 => {
                v___x_3537_ = lean_unsigned_to_nat(0);
                v___x_3538_ = l_Lean_mkOutParamArgsImplicit___closed__0;
                v___x_3539_ = l_Lean_ConstantInfo_type(v_val_3532_);
                lean_inc_ref(v___x_3539_);
                v___x_3540_ = l___private_Lean_Class_0__Lean_checkOutParam(
                    v___x_3537_,
                    v___x_3538_,
                    v___x_3538_,
                    v___x_3539_,
                );
                if lean_obj_tag(v___x_3540_) == 0 {
                    lean_dec_ref(v___x_3539_);
                    lean_dec(v_val_3532_);
                    lean_dec(v_clsName_3529_);
                    lean_dec_ref(v_env_3528_);
                    v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
                    v_isSharedCheck_3548_ = (!lean_is_exclusive(v___x_3540_)) as u8;
                    if v_isSharedCheck_3548_ == 0 {
                        v___x_3543_ = v___x_3540_;
                        v_isShared_3544_ = v_isSharedCheck_3548_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3541_);
                        lean_dec(v___x_3540_);
                        v___x_3543_ = lean_box(0);
                        v_isShared_3544_ = v_isSharedCheck_3548_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_3549_ = lean_ctor_get(v___x_3540_, 0);
                    v_isSharedCheck_3564_ = (!lean_is_exclusive(v___x_3540_)) as u8;
                    if v_isSharedCheck_3564_ == 0 {
                        v___x_3551_ = v___x_3540_;
                        v_isShared_3552_ = v_isSharedCheck_3564_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3549_);
                        lean_dec(v___x_3540_);
                        v___x_3551_ = lean_box(0);
                        v_isShared_3552_ = v_isSharedCheck_3564_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3544_ == 0 {
                    v___x_3546_ = v___x_3543_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
                    v___x_3546_ = v_reuseFailAlloc_3547_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3546_;
            }
            5 => {
                v___x_3553_ = l_Lean_classExtension;
                v_toEnvExtension_3554_ = lean_ctor_get(v___x_3553_, 0);
                v_asyncMode_3555_ = lean_ctor_get(v_toEnvExtension_3554_, 2);
                v___x_3556_ = l_Lean_ConstantInfo_levelParams(v_val_3532_);
                lean_dec(v_val_3532_);
                v___x_3557_ = l___private_Lean_Class_0__Lean_computeOutLevelParams(
                    v___x_3539_,
                    v_a_3549_,
                    v___x_3556_,
                );
                lean_dec(v___x_3556_);
                v___x_3558_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_3558_, 0, v_clsName_3529_);
                lean_ctor_set(v___x_3558_, 1, v_a_3549_);
                lean_ctor_set(v___x_3558_, 2, v___x_3557_);
                v___x_3559_ = lean_box(0);
                v___x_3560_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3553_,
                    v_env_3528_,
                    v___x_3558_,
                    v_asyncMode_3555_,
                    v___x_3559_,
                );
                if v_isShared_3552_ == 0 {
                    lean_ctor_set(v___x_3551_, 0, v___x_3560_);
                    v___x_3562_ = v___x_3551_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
                    v___x_3562_ = v_reuseFailAlloc_3563_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3562_;
            }
            7 => {
                return v___x_3571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3586_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    v___x_3587_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__0_once), _init_l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__0);
    v___x_3588_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3588_, 0, v___x_3587_);
    return v___x_3588_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    v___x_3589_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__1_once), _init_l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__1);
    v___x_3590_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3590_, 0, v___x_3589_);
    lean_ctor_set(v___x_3590_, 1, v___x_3589_);
    return v___x_3590_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg(
    mut v_env_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3612_: u8 = 0;
    let mut v_unused_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3594_ = lean_st_ref_take(v___y_3592_);
                v_nextMacroScope_3595_ = lean_ctor_get(v___x_3594_, 1);
                v_ngen_3596_ = lean_ctor_get(v___x_3594_, 2);
                v_auxDeclNGen_3597_ = lean_ctor_get(v___x_3594_, 3);
                v_traceState_3598_ = lean_ctor_get(v___x_3594_, 4);
                v_messages_3599_ = lean_ctor_get(v___x_3594_, 6);
                v_infoState_3600_ = lean_ctor_get(v___x_3594_, 7);
                v_snapshotTasks_3601_ = lean_ctor_get(v___x_3594_, 8);
                v_isSharedCheck_3612_ = (!lean_is_exclusive(v___x_3594_)) as u8;
                if v_isSharedCheck_3612_ == 0 {
                    v_unused_3613_ = lean_ctor_get(v___x_3594_, 5);
                    lean_dec(v_unused_3613_);
                    v_unused_3614_ = lean_ctor_get(v___x_3594_, 0);
                    lean_dec(v_unused_3614_);
                    v___x_3603_ = v___x_3594_;
                    v_isShared_3604_ = v_isSharedCheck_3612_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3601_);
                    lean_inc(v_infoState_3600_);
                    lean_inc(v_messages_3599_);
                    lean_inc(v_traceState_3598_);
                    lean_inc(v_auxDeclNGen_3597_);
                    lean_inc(v_ngen_3596_);
                    lean_inc(v_nextMacroScope_3595_);
                    lean_dec(v___x_3594_);
                    v___x_3603_ = lean_box(0);
                    v_isShared_3604_ = v_isSharedCheck_3612_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3605_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2_once), _init_l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2);
                if v_isShared_3604_ == 0 {
                    lean_ctor_set(v___x_3603_, 5, v___x_3605_);
                    lean_ctor_set(v___x_3603_, 0, v_env_3591_);
                    v___x_3607_ = v___x_3603_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_env_3591_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_nextMacroScope_3595_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_ngen_3596_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_auxDeclNGen_3597_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_traceState_3598_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 5, v___x_3605_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 6, v_messages_3599_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 7, v_infoState_3600_);
                    lean_ctor_set(v_reuseFailAlloc_3611_, 8, v_snapshotTasks_3601_);
                    v___x_3607_ = v_reuseFailAlloc_3611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3608_ = lean_st_ref_set(v___y_3592_, v___x_3607_);
                v___x_3609_ = lean_box(0);
                v___x_3610_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3610_, 0, v___x_3609_);
                return v___x_3610_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___boxed(
    mut v_env_3615_: *mut LeanObject,
    mut v___y_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3618_: *mut LeanObject = core::ptr::null_mut();
    v_res_3618_ = l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg(
        v_env_3615_,
        v___y_3616_,
    );
    lean_dec(v___y_3616_);
    return v_res_3618_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2(
    mut v_env_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    v___x_3623_ = l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg(
        v_env_3619_,
        v___y_3621_,
    );
    return v___x_3623_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___boxed(
    mut v_env_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3628_: *mut LeanObject = core::ptr::null_mut();
    v_res_3628_ = l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2(
        v_env_3624_,
        v___y_3625_,
        v___y_3626_,
    );
    lean_dec(v___y_3626_);
    lean_dec_ref(v___y_3625_);
    return v_res_3628_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    v___x_3629_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3629_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    v___x_3630_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__0);
    v___x_3631_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3631_, 0, v___x_3630_);
    return v___x_3631_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    v___x_3632_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1);
    v___x_3633_ = lean_unsigned_to_nat(0);
    v___x_3634_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3634_, 0, v___x_3633_);
    lean_ctor_set(v___x_3634_, 1, v___x_3633_);
    lean_ctor_set(v___x_3634_, 2, v___x_3633_);
    lean_ctor_set(v___x_3634_, 3, v___x_3633_);
    lean_ctor_set(v___x_3634_, 4, v___x_3632_);
    lean_ctor_set(v___x_3634_, 5, v___x_3632_);
    lean_ctor_set(v___x_3634_, 6, v___x_3632_);
    lean_ctor_set(v___x_3634_, 7, v___x_3632_);
    lean_ctor_set(v___x_3634_, 8, v___x_3632_);
    lean_ctor_set(v___x_3634_, 9, v___x_3632_);
    return v___x_3634_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    v___x_3635_ = lean_unsigned_to_nat(32);
    v___x_3636_ = lean_mk_empty_array_with_capacity(v___x_3635_);
    v___x_3637_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3637_, 0, v___x_3636_);
    return v___x_3637_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_3638_: usize = 0;
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    v___x_3638_ = 5usize;
    v___x_3639_ = lean_unsigned_to_nat(0);
    v___x_3640_ = lean_unsigned_to_nat(32);
    v___x_3641_ = lean_mk_empty_array_with_capacity(v___x_3640_);
    v___x_3642_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__3);
    v___x_3643_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3643_, 0, v___x_3642_);
    lean_ctor_set(v___x_3643_, 1, v___x_3641_);
    lean_ctor_set(v___x_3643_, 2, v___x_3639_);
    lean_ctor_set(v___x_3643_, 3, v___x_3639_);
    lean_ctor_set_usize(v___x_3643_, 4, v___x_3638_);
    return v___x_3643_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    v___x_3644_ = lean_box(1);
    v___x_3645_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__4);
    v___x_3646_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__1);
    v___x_3647_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3647_, 0, v___x_3646_);
    lean_ctor_set(v___x_3647_, 1, v___x_3645_);
    lean_ctor_set(v___x_3647_, 2, v___x_3644_);
    return v___x_3647_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0(
    mut v_msgData_3648_: *mut LeanObject,
    mut v___y_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    v___x_3652_ = lean_st_ref_get(v___y_3650_);
    v_env_3653_ = lean_ctor_get(v___x_3652_, 0);
    lean_inc_ref(v_env_3653_);
    lean_dec(v___x_3652_);
    v_options_3654_ = lean_ctor_get(v___y_3649_, 2);
    v___x_3655_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2);
    v___x_3656_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_3654_);
    v___x_3657_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3657_, 0, v_env_3653_);
    lean_ctor_set(v___x_3657_, 1, v___x_3655_);
    lean_ctor_set(v___x_3657_, 2, v___x_3656_);
    lean_ctor_set(v___x_3657_, 3, v_options_3654_);
    v___x_3658_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3658_, 0, v___x_3657_);
    lean_ctor_set(v___x_3658_, 1, v_msgData_3648_);
    v___x_3659_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3659_, 0, v___x_3658_);
    return v___x_3659_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___boxed(
    mut v_msgData_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
    mut v___y_3662_: *mut LeanObject,
    mut v___y_3663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3664_: *mut LeanObject = core::ptr::null_mut();
    v_res_3664_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0(v_msgData_3660_, v___y_3661_, v___y_3662_);
    lean_dec(v___y_3662_);
    lean_dec_ref(v___y_3661_);
    return v_res_3664_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(
    mut v_msg_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3674_: u8 = 0;
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3669_ = lean_ctor_get(v___y_3666_, 5);
                v___x_3670_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0(v_msg_3665_, v___y_3666_, v___y_3667_);
                v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
                v_isSharedCheck_3679_ = (!lean_is_exclusive(v___x_3670_)) as u8;
                if v_isSharedCheck_3679_ == 0 {
                    v___x_3673_ = v___x_3670_;
                    v_isShared_3674_ = v_isSharedCheck_3679_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3671_);
                    lean_dec(v___x_3670_);
                    v___x_3673_ = lean_box(0);
                    v_isShared_3674_ = v_isSharedCheck_3679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3669_);
                v___x_3675_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3675_, 0, v_ref_3669_);
                lean_ctor_set(v___x_3675_, 1, v_a_3671_);
                if v_isShared_3674_ == 0 {
                    lean_ctor_set_tag(v___x_3673_, 1);
                    lean_ctor_set(v___x_3673_, 0, v___x_3675_);
                    v___x_3677_ = v___x_3673_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
                    v___x_3677_ = v_reuseFailAlloc_3678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg___boxed(
    mut v_msg_3680_: *mut LeanObject,
    mut v___y_3681_: *mut LeanObject,
    mut v___y_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3684_: *mut LeanObject = core::ptr::null_mut();
    v_res_3684_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(
        v_msg_3680_,
        v___y_3681_,
        v___y_3682_,
    );
    lean_dec(v___y_3682_);
    lean_dec_ref(v___y_3681_);
    return v_res_3684_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1___redArg(
    mut v_x_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3685_) == 0 {
                    v_a_3689_ = lean_ctor_get(v_x_3685_, 0);
                    lean_inc(v_a_3689_);
                    lean_dec_ref_known(v_x_3685_, 1);
                    v___x_3690_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(v_a_3689_, v___y_3686_, v___y_3687_);
                    return v___x_3690_;
                } else {
                    v_a_3691_ = lean_ctor_get(v_x_3685_, 0);
                    v_isSharedCheck_3698_ = (!lean_is_exclusive(v_x_3685_)) as u8;
                    if v_isSharedCheck_3698_ == 0 {
                        v___x_3693_ = v_x_3685_;
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3691_);
                        lean_dec(v_x_3685_);
                        v___x_3693_ = lean_box(0);
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3694_ == 0 {
                    lean_ctor_set_tag(v___x_3693_, 0);
                    v___x_3696_ = v___x_3693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
                    v___x_3696_ = v_reuseFailAlloc_3697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1___redArg___boxed(
    mut v_x_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
    mut v___y_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3703_: *mut LeanObject = core::ptr::null_mut();
    v_res_3703_ = l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1___redArg(
        v_x_3699_,
        v___y_3700_,
        v___y_3701_,
    );
    lean_dec(v___y_3701_);
    lean_dec_ref(v___y_3700_);
    return v_res_3703_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    v___x_3705_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__0;
    v___x_3706_ = l_Lean_stringToMessageData(v___x_3705_);
    return v___x_3706_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    v___x_3708_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__2;
    v___x_3709_ = l_Lean_stringToMessageData(v___x_3708_);
    return v___x_3709_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    v___x_3711_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__4;
    v___x_3712_ = l_Lean_stringToMessageData(v___x_3711_);
    return v___x_3712_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg(
    mut v_name_3716_: *mut LeanObject,
    mut v_kind_3717_: u8,
    mut v___y_3718_: *mut LeanObject,
    mut v___y_3719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3721_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__1);
                v___x_3722_ = l_Lean_MessageData_ofName(v_name_3716_);
                v___x_3723_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3723_, 0, v___x_3721_);
                lean_ctor_set(v___x_3723_, 1, v___x_3722_);
                v___x_3724_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__3);
                v___x_3725_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3725_, 0, v___x_3723_);
                lean_ctor_set(v___x_3725_, 1, v___x_3724_);
                match v_kind_3717_ {
                    0 => {
                        v___x_3734_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__6;
                        v___y_3727_ = v___x_3734_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_3735_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__7;
                        v___y_3727_ = v___x_3735_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_3736_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__8;
                        v___y_3727_ = v___x_3736_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_3727_);
                v___x_3728_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3728_, 0, v___y_3727_);
                v___x_3729_ = l_Lean_MessageData_ofFormat(v___x_3728_);
                v___x_3730_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3730_, 0, v___x_3725_);
                lean_ctor_set(v___x_3730_, 1, v___x_3729_);
                v___x_3731_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5);
                v___x_3732_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3732_, 0, v___x_3730_);
                lean_ctor_set(v___x_3732_, 1, v___x_3731_);
                v___x_3733_ =
                    l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(
                        v___x_3732_,
                        v___y_3718_,
                        v___y_3719_,
                    );
                return v___x_3733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___boxed(
    mut v_name_3737_: *mut LeanObject,
    mut v_kind_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3742_: u8 = 0;
    let mut v_res_3743_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3742_ = (lean_unbox(v_kind_3738_) as u8);
    v_res_3743_ =
        l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg(
            v_name_3737_,
            v_kind_boxed_3742_,
            v___y_3739_,
            v___y_3740_,
        );
    lean_dec(v___y_3740_);
    lean_dec_ref(v___y_3739_);
    return v_res_3743_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_init___lam__0(
    mut v___x_3744_: *mut LeanObject,
    mut v_decl_3745_: *mut LeanObject,
    mut v_stx_3746_: *mut LeanObject,
    mut v_kind_3747_: u8,
    mut v___y_3748_: *mut LeanObject,
    mut v___y_3749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3768_: u8 = 0;
    let mut v___x_3769_: u8 = 0;
    let mut v___x_3770_: u8 = 0;
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3751_ = lean_st_ref_get(v___y_3749_);
                v___x_3752_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3746_, v___y_3748_, v___y_3749_);
                if lean_obj_tag(v___x_3752_) == 0 {
                    lean_dec_ref_known(v___x_3752_, 1);
                    v_env_3753_ = lean_ctor_get(v___x_3751_, 0);
                    lean_inc_ref(v_env_3753_);
                    lean_dec(v___x_3751_);
                    v___x_3769_ = 0;
                    v___x_3770_ = l_Lean_instBEqAttributeKind_beq(v_kind_3747_, v___x_3769_);
                    if v___x_3770_ == 0 {
                        lean_dec_ref(v_env_3753_);
                        lean_dec(v_decl_3745_);
                        v___x_3771_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg(v___x_3744_, v_kind_3747_, v___y_3748_, v___y_3749_);
                        return v___x_3771_;
                    } else {
                        lean_dec(v___x_3744_);
                        v___y_3755_ = v___y_3748_;
                        v___y_3756_ = v___y_3749_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3751_);
                    lean_dec(v_decl_3745_);
                    lean_dec(v___x_3744_);
                    return v___x_3752_;
                }
            }
            1 => {
                v___x_3757_ = l_Lean_addClass(v_env_3753_, v_decl_3745_);
                v___x_3758_ =
                    l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1___redArg(
                        v___x_3757_,
                        v___y_3755_,
                        v___y_3756_,
                    );
                if lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
                    lean_inc(v_a_3759_);
                    lean_dec_ref_known(v___x_3758_, 1);
                    v___x_3760_ =
                        l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg(
                            v_a_3759_,
                            v___y_3756_,
                        );
                    return v___x_3760_;
                } else {
                    v_a_3761_ = lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3768_ = (!lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3768_ == 0 {
                        v___x_3763_ = v___x_3758_;
                        v_isShared_3764_ = v_isSharedCheck_3768_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3761_);
                        lean_dec(v___x_3758_);
                        v___x_3763_ = lean_box(0);
                        v_isShared_3764_ = v_isSharedCheck_3768_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3764_ == 0 {
                    v___x_3766_ = v___x_3763_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
                    v___x_3766_ = v_reuseFailAlloc_3767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Class_0__Lean_init___lam__0___boxed(
    mut v___x_3772_: *mut LeanObject,
    mut v_decl_3773_: *mut LeanObject,
    mut v_stx_3774_: *mut LeanObject,
    mut v_kind_3775_: *mut LeanObject,
    mut v___y_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3779_: u8 = 0;
    let mut v_res_3780_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3779_ = (lean_unbox(v_kind_3775_) as u8);
    v_res_3780_ = l___private_Lean_Class_0__Lean_init___lam__0(
        v___x_3772_,
        v_decl_3773_,
        v_stx_3774_,
        v_kind_boxed_3779_,
        v___y_3776_,
        v___y_3777_,
    );
    lean_dec(v___y_3777_);
    lean_dec_ref(v___y_3776_);
    return v_res_3780_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_init___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ = l___private_Lean_Class_0__Lean_init___lam__1___closed__0;
    v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_init___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3785_ = l___private_Lean_Class_0__Lean_init___lam__1___closed__2;
    v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_init___lam__1(
    mut v___x_3787_: *mut LeanObject,
    mut v_decl_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    v___x_3792_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__1),
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__1_once),
        _init_l___private_Lean_Class_0__Lean_init___lam__1___closed__1,
    );
    v___x_3793_ = l_Lean_MessageData_ofName(v___x_3787_);
    v___x_3794_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3794_, 0, v___x_3792_);
    lean_ctor_set(v___x_3794_, 1, v___x_3793_);
    v___x_3795_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__3),
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__3_once),
        _init_l___private_Lean_Class_0__Lean_init___lam__1___closed__3,
    );
    v___x_3796_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3796_, 0, v___x_3794_);
    lean_ctor_set(v___x_3796_, 1, v___x_3795_);
    v___x_3797_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(
        v___x_3796_,
        v___y_3789_,
        v___y_3790_,
    );
    return v___x_3797_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_init___lam__1___boxed(
    mut v___x_3798_: *mut LeanObject,
    mut v_decl_3799_: *mut LeanObject,
    mut v___y_3800_: *mut LeanObject,
    mut v___y_3801_: *mut LeanObject,
    mut v___y_3802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3803_: *mut LeanObject = core::ptr::null_mut();
    v_res_3803_ = l___private_Lean_Class_0__Lean_init___lam__1(
        v___x_3798_,
        v_decl_3799_,
        v___y_3800_,
        v___y_3801_,
    );
    lean_dec(v___y_3801_);
    lean_dec_ref(v___y_3800_);
    lean_dec(v_decl_3799_);
    return v_res_3803_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_init() -> *mut LeanObject {
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    v___x_3843_ = l___private_Lean_Class_0__Lean_init___closed__15;
    v___x_3844_ = l_Lean_registerBuiltinAttribute(v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_init___boxed(
    mut v_a_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3846_: *mut LeanObject = core::ptr::null_mut();
    v_res_3846_ = l___private_Lean_Class_0__Lean_init();
    return v_res_3846_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0(
    mut v_00_u03b1_3847_: *mut LeanObject,
    mut v_msg_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
    mut v___y_3850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(
        v_msg_3848_,
        v___y_3849_,
        v___y_3850_,
    );
    return v___x_3852_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___boxed(
    mut v_00_u03b1_3853_: *mut LeanObject,
    mut v_msg_3854_: *mut LeanObject,
    mut v___y_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3858_: *mut LeanObject = core::ptr::null_mut();
    v_res_3858_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0(
        v_00_u03b1_3853_,
        v_msg_3854_,
        v___y_3855_,
        v___y_3856_,
    );
    lean_dec(v___y_3856_);
    lean_dec_ref(v___y_3855_);
    return v_res_3858_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1(
    mut v_00_u03b1_3859_: *mut LeanObject,
    mut v_x_3860_: *mut LeanObject,
    mut v___y_3861_: *mut LeanObject,
    mut v___y_3862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    v___x_3864_ = l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1___redArg(
        v_x_3860_,
        v___y_3861_,
        v___y_3862_,
    );
    return v___x_3864_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1___boxed(
    mut v_00_u03b1_3865_: *mut LeanObject,
    mut v_x_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3870_: *mut LeanObject = core::ptr::null_mut();
    v_res_3870_ = l_Lean_ofExcept___at___00__private_Lean_Class_0__Lean_init_spec__1(
        v_00_u03b1_3865_,
        v_x_3866_,
        v___y_3867_,
        v___y_3868_,
    );
    lean_dec(v___y_3868_);
    lean_dec_ref(v___y_3867_);
    return v_res_3870_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3(
    mut v_00_u03b1_3871_: *mut LeanObject,
    mut v_name_3872_: *mut LeanObject,
    mut v_kind_3873_: u8,
    mut v___y_3874_: *mut LeanObject,
    mut v___y_3875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    v___x_3877_ =
        l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg(
            v_name_3872_,
            v_kind_3873_,
            v___y_3874_,
            v___y_3875_,
        );
    return v___x_3877_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___boxed(
    mut v_00_u03b1_3878_: *mut LeanObject,
    mut v_name_3879_: *mut LeanObject,
    mut v_kind_3880_: *mut LeanObject,
    mut v___y_3881_: *mut LeanObject,
    mut v___y_3882_: *mut LeanObject,
    mut v___y_3883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3884_: u8 = 0;
    let mut v_res_3885_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3884_ = (lean_unbox(v_kind_3880_) as u8);
    v_res_3885_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3(
        v_00_u03b1_3878_,
        v_name_3879_,
        v_kind_boxed_3884_,
        v___y_3881_,
        v___y_3882_,
    );
    lean_dec(v___y_3882_);
    lean_dec_ref(v___y_3881_);
    return v_res_3885_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1()
-> *mut LeanObject {
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    v___x_3888_ = l___private_Lean_Class_0__Lean_init___closed__8;
    v___x_3889_ = l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1___closed__0;
    v___x_3890_ = l_Lean_addBuiltinDocString(v___x_3888_, v___x_3889_);
    return v___x_3890_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1___boxed(
    mut v_a_3891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3892_: *mut LeanObject = core::ptr::null_mut();
    v_res_3892_ = l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1();
    return v_res_3892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__3(
    mut v_sz_3893_: usize,
    mut v_i_3894_: usize,
    mut v_bs_3895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3896_: u8 = 0;
    let mut v_v_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: usize = 0;
    let mut v___x_3902_: usize = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3896_ = lean_usize_dec_lt(v_i_3894_, v_sz_3893_);
                if v___x_3896_ == 0 {
                    return v_bs_3895_;
                } else {
                    v_v_3897_ = lean_array_uget(v_bs_3895_, v_i_3894_);
                    v___x_3898_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3899_ = lean_array_uset(v_bs_3895_, v_i_3894_, v___x_3898_);
                    v___x_3900_ = l_Lean_Syntax_getId(v_v_3897_);
                    lean_dec(v_v_3897_);
                    v___x_3901_ = 1usize;
                    v___x_3902_ = lean_usize_add(v_i_3894_, v___x_3901_);
                    v___x_3903_ = lean_array_uset(v_bs_x27_3899_, v_i_3894_, v___x_3900_);
                    v_i_3894_ = v___x_3902_;
                    v_bs_3895_ = v___x_3903_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__3___boxed(
    mut v_sz_3905_: *mut LeanObject,
    mut v_i_3906_: *mut LeanObject,
    mut v_bs_3907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3908_: usize = 0;
    let mut v_i_boxed_3909_: usize = 0;
    let mut v_res_3910_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3908_ = lean_unbox_usize(v_sz_3905_);
    lean_dec(v_sz_3905_);
    v_i_boxed_3909_ = lean_unbox_usize(v_i_3906_);
    lean_dec(v_i_3906_);
    v_res_3910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__3(v_sz_boxed_3908_, v_i_boxed_3909_, v_bs_3907_);
    return v_res_3910_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2___redArg(
    mut v_ref_3911_: *mut LeanObject,
    mut v_msg_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3928_: u8 = 0;
    let mut v_cancelTk_x3f_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3930_: u8 = 0;
    let mut v_inheritedTraceOptions_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3916_ = lean_ctor_get(v___y_3913_, 0);
    v_fileMap_3917_ = lean_ctor_get(v___y_3913_, 1);
    v_options_3918_ = lean_ctor_get(v___y_3913_, 2);
    v_currRecDepth_3919_ = lean_ctor_get(v___y_3913_, 3);
    v_maxRecDepth_3920_ = lean_ctor_get(v___y_3913_, 4);
    v_ref_3921_ = lean_ctor_get(v___y_3913_, 5);
    v_currNamespace_3922_ = lean_ctor_get(v___y_3913_, 6);
    v_openDecls_3923_ = lean_ctor_get(v___y_3913_, 7);
    v_initHeartbeats_3924_ = lean_ctor_get(v___y_3913_, 8);
    v_maxHeartbeats_3925_ = lean_ctor_get(v___y_3913_, 9);
    v_quotContext_3926_ = lean_ctor_get(v___y_3913_, 10);
    v_currMacroScope_3927_ = lean_ctor_get(v___y_3913_, 11);
    v_diag_3928_ = lean_ctor_get_uint8(
        v___y_3913_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3929_ = lean_ctor_get(v___y_3913_, 12);
    v_suppressElabErrors_3930_ = lean_ctor_get_uint8(
        v___y_3913_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3931_ = lean_ctor_get(v___y_3913_, 13);
    v_ref_3932_ = l_Lean_replaceRef(v_ref_3911_, v_ref_3921_);
    lean_inc_ref(v_inheritedTraceOptions_3931_);
    lean_inc(v_cancelTk_x3f_3929_);
    lean_inc(v_currMacroScope_3927_);
    lean_inc(v_quotContext_3926_);
    lean_inc(v_maxHeartbeats_3925_);
    lean_inc(v_initHeartbeats_3924_);
    lean_inc(v_openDecls_3923_);
    lean_inc(v_currNamespace_3922_);
    lean_inc(v_maxRecDepth_3920_);
    lean_inc(v_currRecDepth_3919_);
    lean_inc_ref(v_options_3918_);
    lean_inc_ref(v_fileMap_3917_);
    lean_inc_ref(v_fileName_3916_);
    v___x_3933_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3933_, 0, v_fileName_3916_);
    lean_ctor_set(v___x_3933_, 1, v_fileMap_3917_);
    lean_ctor_set(v___x_3933_, 2, v_options_3918_);
    lean_ctor_set(v___x_3933_, 3, v_currRecDepth_3919_);
    lean_ctor_set(v___x_3933_, 4, v_maxRecDepth_3920_);
    lean_ctor_set(v___x_3933_, 5, v_ref_3932_);
    lean_ctor_set(v___x_3933_, 6, v_currNamespace_3922_);
    lean_ctor_set(v___x_3933_, 7, v_openDecls_3923_);
    lean_ctor_set(v___x_3933_, 8, v_initHeartbeats_3924_);
    lean_ctor_set(v___x_3933_, 9, v_maxHeartbeats_3925_);
    lean_ctor_set(v___x_3933_, 10, v_quotContext_3926_);
    lean_ctor_set(v___x_3933_, 11, v_currMacroScope_3927_);
    lean_ctor_set(v___x_3933_, 12, v_cancelTk_x3f_3929_);
    lean_ctor_set(v___x_3933_, 13, v_inheritedTraceOptions_3931_);
    lean_ctor_set_uint8(
        v___x_3933_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3928_,
    );
    lean_ctor_set_uint8(
        v___x_3933_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3930_,
    );
    v___x_3934_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(
        v_msg_3912_,
        v___x_3933_,
        v___y_3914_,
    );
    lean_dec_ref_known(v___x_3933_, 14);
    return v___x_3934_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_ref_3935_: *mut LeanObject,
    mut v_msg_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
    mut v___y_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3940_: *mut LeanObject = core::ptr::null_mut();
    v_res_3940_ = l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2___redArg(v_ref_3935_, v_msg_3936_, v___y_3937_, v___y_3938_);
    lean_dec(v___y_3938_);
    lean_dec_ref(v___y_3937_);
    lean_dec(v_ref_3935_);
    return v_res_3940_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__0;
    v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
    return v___x_3943_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__2;
    v___x_3946_ = l_Lean_stringToMessageData(v___x_3945_);
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    v___x_3948_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__4;
    v___x_3949_ = l_Lean_stringToMessageData(v___x_3948_);
    return v___x_3949_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_3952_ = l_Lean_stringToMessageData(v___x_3951_);
    return v___x_3952_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    v___x_3954_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_3955_ = l_Lean_stringToMessageData(v___x_3954_);
    return v___x_3955_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_3958_ = l_Lean_stringToMessageData(v___x_3957_);
    return v___x_3958_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_3961_ = l_Lean_stringToMessageData(v___x_3960_);
    return v___x_3961_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(
    mut v_msg_3962_: *mut LeanObject,
    mut v_declHint_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v_isExporting_3969_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: u8 = 0;
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3991_: u8 = 0;
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: u8 = 0;
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4023_: u8 = 0;
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3966_ = lean_st_ref_get(v___y_3964_);
                v_env_3967_ = lean_ctor_get(v___x_3966_, 0);
                lean_inc_ref(v_env_3967_);
                lean_dec(v___x_3966_);
                v___x_3968_ = l_Lean_Name_isAnonymous(v_declHint_3963_);
                if v___x_3968_ == 0 {
                    v_isExporting_3969_ = lean_ctor_get_uint8(
                        v_env_3967_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3969_ == 0 {
                        lean_dec_ref(v_env_3967_);
                        lean_dec(v_declHint_3963_);
                        v___x_3970_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3970_, 0, v_msg_3962_);
                        return v___x_3970_;
                    } else {
                        lean_inc_ref(v_env_3967_);
                        v___x_3971_ = l_Lean_Environment_setExporting(v_env_3967_, v___x_3968_);
                        lean_inc(v_declHint_3963_);
                        lean_inc_ref(v___x_3971_);
                        v___x_3972_ = l_Lean_Environment_contains(
                            v___x_3971_,
                            v_declHint_3963_,
                            v_isExporting_3969_,
                        );
                        if v___x_3972_ == 0 {
                            lean_dec_ref(v___x_3971_);
                            lean_dec_ref(v_env_3967_);
                            lean_dec(v_declHint_3963_);
                            v___x_3973_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3973_, 0, v_msg_3962_);
                            return v___x_3973_;
                        } else {
                            v___x_3974_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__2);
                            v___x_3975_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0_spec__0___closed__5);
                            v___x_3976_ = l_Lean_Options_empty;
                            v___x_3977_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3977_, 0, v___x_3971_);
                            lean_ctor_set(v___x_3977_, 1, v___x_3974_);
                            lean_ctor_set(v___x_3977_, 2, v___x_3975_);
                            lean_ctor_set(v___x_3977_, 3, v___x_3976_);
                            lean_inc(v_declHint_3963_);
                            v___x_3978_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3963_, v___x_3968_);
                            v_c_3979_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3979_, 0, v___x_3977_);
                            lean_ctor_set(v_c_3979_, 1, v___x_3978_);
                            v___x_3980_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3967_,
                                v_declHint_3963_,
                            );
                            if lean_obj_tag(v___x_3980_) == 0 {
                                lean_dec_ref(v_env_3967_);
                                lean_dec(v_declHint_3963_);
                                v___x_3981_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
                                v___x_3982_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3982_, 0, v___x_3981_);
                                lean_ctor_set(v___x_3982_, 1, v_c_3979_);
                                v___x_3983_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__3);
                                v___x_3984_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3984_, 0, v___x_3982_);
                                lean_ctor_set(v___x_3984_, 1, v___x_3983_);
                                v___x_3985_ = l_Lean_MessageData_note(v___x_3984_);
                                v___x_3986_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3986_, 0, v_msg_3962_);
                                lean_ctor_set(v___x_3986_, 1, v___x_3985_);
                                v___x_3987_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3987_, 0, v___x_3986_);
                                return v___x_3987_;
                            } else {
                                v_val_3988_ = lean_ctor_get(v___x_3980_, 0);
                                v_isSharedCheck_4023_ = (!lean_is_exclusive(v___x_3980_)) as u8;
                                if v_isSharedCheck_4023_ == 0 {
                                    v___x_3990_ = v___x_3980_;
                                    v_isShared_3991_ = v_isSharedCheck_4023_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3988_);
                                    lean_dec(v___x_3980_);
                                    v___x_3990_ = lean_box(0);
                                    v_isShared_3991_ = v_isSharedCheck_4023_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3967_);
                    lean_dec(v_declHint_3963_);
                    v___x_4024_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4024_, 0, v_msg_3962_);
                    return v___x_4024_;
                }
            }
            1 => {
                v___x_3992_ = lean_box(0);
                v___x_3993_ = l_Lean_Environment_header(v_env_3967_);
                lean_dec_ref(v_env_3967_);
                v___x_3994_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3993_);
                v_mod_3995_ = lean_array_get(v___x_3992_, v___x_3994_, v_val_3988_);
                lean_dec(v_val_3988_);
                lean_dec_ref(v___x_3994_);
                v___x_3996_ = l_Lean_isPrivateName(v_declHint_3963_);
                lean_dec(v_declHint_3963_);
                if v___x_3996_ == 0 {
                    v___x_3997_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__5);
                    v___x_3998_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3998_, 0, v___x_3997_);
                    lean_ctor_set(v___x_3998_, 1, v_c_3979_);
                    v___x_3999_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_4000_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4000_, 0, v___x_3998_);
                    lean_ctor_set(v___x_4000_, 1, v___x_3999_);
                    v___x_4001_ = l_Lean_MessageData_ofName(v_mod_3995_);
                    v___x_4002_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4002_, 0, v___x_4000_);
                    lean_ctor_set(v___x_4002_, 1, v___x_4001_);
                    v___x_4003_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__9);
                    v___x_4004_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4004_, 0, v___x_4002_);
                    lean_ctor_set(v___x_4004_, 1, v___x_4003_);
                    v___x_4005_ = l_Lean_MessageData_note(v___x_4004_);
                    v___x_4006_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4006_, 0, v_msg_3962_);
                    lean_ctor_set(v___x_4006_, 1, v___x_4005_);
                    if v_isShared_3991_ == 0 {
                        lean_ctor_set_tag(v___x_3990_, 0);
                        lean_ctor_set(v___x_3990_, 0, v___x_4006_);
                        v___x_4008_ = v___x_3990_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4006_);
                        v___x_4008_ = v_reuseFailAlloc_4009_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4010_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__1);
                    v___x_4011_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4011_, 0, v___x_4010_);
                    lean_ctor_set(v___x_4011_, 1, v_c_3979_);
                    v___x_4012_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_4013_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4013_, 0, v___x_4011_);
                    lean_ctor_set(v___x_4013_, 1, v___x_4012_);
                    v___x_4014_ = l_Lean_MessageData_ofName(v_mod_3995_);
                    v___x_4015_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4015_, 0, v___x_4013_);
                    lean_ctor_set(v___x_4015_, 1, v___x_4014_);
                    v___x_4016_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_4017_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4017_, 0, v___x_4015_);
                    lean_ctor_set(v___x_4017_, 1, v___x_4016_);
                    v___x_4018_ = l_Lean_MessageData_note(v___x_4017_);
                    v___x_4019_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4019_, 0, v_msg_3962_);
                    lean_ctor_set(v___x_4019_, 1, v___x_4018_);
                    if v_isShared_3991_ == 0 {
                        lean_ctor_set_tag(v___x_3990_, 0);
                        lean_ctor_set(v___x_3990_, 0, v___x_4019_);
                        v___x_4021_ = v___x_3990_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4019_);
                        v___x_4021_ = v_reuseFailAlloc_4022_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4008_;
            }
            3 => {
                return v___x_4021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_4025_: *mut LeanObject,
    mut v_declHint_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4029_: *mut LeanObject = core::ptr::null_mut();
    v_res_4029_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_4025_, v_declHint_4026_, v___y_4027_);
    lean_dec(v___y_4027_);
    return v_res_4029_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8(
    mut v_msg_4030_: *mut LeanObject,
    mut v_declHint_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4039_: u8 = 0;
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4035_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_4030_, v_declHint_4031_, v___y_4033_);
                v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
                v_isSharedCheck_4045_ = (!lean_is_exclusive(v___x_4035_)) as u8;
                if v_isSharedCheck_4045_ == 0 {
                    v___x_4038_ = v___x_4035_;
                    v_isShared_4039_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4036_);
                    lean_dec(v___x_4035_);
                    v___x_4038_ = lean_box(0);
                    v_isShared_4039_ = v_isSharedCheck_4045_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4040_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4041_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4041_, 0, v___x_4040_);
                lean_ctor_set(v___x_4041_, 1, v_a_4036_);
                if v_isShared_4039_ == 0 {
                    lean_ctor_set(v___x_4038_, 0, v___x_4041_);
                    v___x_4043_ = v___x_4038_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4044_, 0, v___x_4041_);
                    v___x_4043_ = v_reuseFailAlloc_4044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8___boxed(
    mut v_msg_4046_: *mut LeanObject,
    mut v_declHint_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4051_: *mut LeanObject = core::ptr::null_mut();
    v_res_4051_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_4046_, v_declHint_4047_, v___y_4048_, v___y_4049_);
    lean_dec(v___y_4049_);
    lean_dec_ref(v___y_4048_);
    return v_res_4051_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7___redArg(
    mut v_ref_4052_: *mut LeanObject,
    mut v_msg_4053_: *mut LeanObject,
    mut v_declHint_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
    mut v___y_4056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    v___x_4058_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8(v_msg_4053_, v_declHint_4054_, v___y_4055_, v___y_4056_);
    v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
    lean_inc(v_a_4059_);
    lean_dec_ref(v___x_4058_);
    v___x_4060_ = l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2___redArg(v_ref_4052_, v_a_4059_, v___y_4055_, v___y_4056_);
    return v___x_4060_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7___redArg___boxed(
    mut v_ref_4061_: *mut LeanObject,
    mut v_msg_4062_: *mut LeanObject,
    mut v_declHint_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4067_: *mut LeanObject = core::ptr::null_mut();
    v_res_4067_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7___redArg(v_ref_4061_, v_msg_4062_, v_declHint_4063_, v___y_4064_, v___y_4065_);
    lean_dec(v___y_4065_);
    lean_dec_ref(v___y_4064_);
    lean_dec(v_ref_4061_);
    return v_res_4067_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    v___x_4069_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
    return v___x_4070_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_ref_4071_: *mut LeanObject,
    mut v_constName_4072_: *mut LeanObject,
    mut v___y_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    v___x_4076_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4077_ = 0;
    lean_inc(v_constName_4072_);
    v___x_4078_ = l_Lean_MessageData_ofConstName(v_constName_4072_, v___x_4077_);
    v___x_4079_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4079_, 0, v___x_4076_);
    lean_ctor_set(v___x_4079_, 1, v___x_4078_);
    v___x_4080_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5);
    v___x_4081_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4081_, 0, v___x_4079_);
    lean_ctor_set(v___x_4081_, 1, v___x_4080_);
    v___x_4082_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7___redArg(v_ref_4071_, v___x_4081_, v_constName_4072_, v___y_4073_, v___y_4074_);
    return v___x_4082_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4083_: *mut LeanObject,
    mut v_constName_4084_: *mut LeanObject,
    mut v___y_4085_: *mut LeanObject,
    mut v___y_4086_: *mut LeanObject,
    mut v___y_4087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4088_: *mut LeanObject = core::ptr::null_mut();
    v_res_4088_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_4083_, v_constName_4084_, v___y_4085_, v___y_4086_);
    lean_dec(v___y_4086_);
    lean_dec_ref(v___y_4085_);
    lean_dec(v_ref_4083_);
    return v_res_4088_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_constName_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4093_ = lean_ctor_get(v___y_4090_, 5);
    v___x_4094_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_4093_, v_constName_4089_, v___y_4090_, v___y_4091_);
    return v___x_4094_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_constName_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4099_: *mut LeanObject = core::ptr::null_mut();
    v_res_4099_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_4095_, v___y_4096_, v___y_4097_);
    lean_dec(v___y_4097_);
    lean_dec_ref(v___y_4096_);
    return v_res_4099_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0(
    mut v_constName_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4112_: u8 = 0;
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4104_ = lean_st_ref_get(v___y_4102_);
                v_env_4105_ = lean_ctor_get(v___x_4104_, 0);
                lean_inc_ref(v_env_4105_);
                lean_dec(v___x_4104_);
                v___x_4106_ = 0;
                lean_inc(v_constName_4100_);
                v___x_4107_ =
                    l_Lean_Environment_find_x3f(v_env_4105_, v_constName_4100_, v___x_4106_);
                if lean_obj_tag(v___x_4107_) == 0 {
                    v___x_4108_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_4100_, v___y_4101_, v___y_4102_);
                    return v___x_4108_;
                } else {
                    lean_dec(v_constName_4100_);
                    v_val_4109_ = lean_ctor_get(v___x_4107_, 0);
                    v_isSharedCheck_4116_ = (!lean_is_exclusive(v___x_4107_)) as u8;
                    if v_isSharedCheck_4116_ == 0 {
                        v___x_4111_ = v___x_4107_;
                        v_isShared_4112_ = v_isSharedCheck_4116_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4109_);
                        lean_dec(v___x_4107_);
                        v___x_4111_ = lean_box(0);
                        v_isShared_4112_ = v_isSharedCheck_4116_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4112_ == 0 {
                    lean_ctor_set_tag(v___x_4111_, 0);
                    v___x_4114_ = v___x_4111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_val_4109_);
                    v___x_4114_ = v_reuseFailAlloc_4115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0___boxed(
    mut v_constName_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4121_: *mut LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0(v_constName_4117_, v___y_4118_, v___y_4119_);
    lean_dec(v___y_4119_);
    lean_dec_ref(v___y_4118_);
    return v_res_4121_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4___redArg(
    mut v___x_4122_: *mut LeanObject,
    mut v_as_x27_4123_: *mut LeanObject,
    mut v_b_4124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outLevelParams_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: u8 = 0;
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4144_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4123_) == 0 {
                    v___x_4126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4126_, 0, v_b_4124_);
                    return v___x_4126_;
                } else {
                    v_head_4127_ = lean_ctor_get(v_as_x27_4123_, 0);
                    v_tail_4128_ = lean_ctor_get(v_as_x27_4123_, 1);
                    v_fst_4129_ = lean_ctor_get(v_b_4124_, 0);
                    v_snd_4130_ = lean_ctor_get(v_b_4124_, 1);
                    v_isSharedCheck_4144_ = (!lean_is_exclusive(v_b_4124_)) as u8;
                    if v_isSharedCheck_4144_ == 0 {
                        v___x_4132_ = v_b_4124_;
                        v_isShared_4133_ = v_isSharedCheck_4144_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4130_);
                        lean_inc(v_fst_4129_);
                        lean_dec(v_b_4124_);
                        v___x_4132_ = lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4144_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4134_ = lean_unsigned_to_nat(1);
                v___x_4142_ = l_Array_contains___at___00__private_Lean_Class_0__Lean_computeOutLevelParams_spec__0(v___x_4122_, v_head_4127_);
                if v___x_4142_ == 0 {
                    v_outLevelParams_4136_ = v_fst_4129_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4130_);
                    v___x_4143_ = lean_array_push(v_fst_4129_, v_snd_4130_);
                    v_outLevelParams_4136_ = v___x_4143_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4137_ = lean_nat_add(v_snd_4130_, v___x_4134_);
                lean_dec(v_snd_4130_);
                if v_isShared_4133_ == 0 {
                    lean_ctor_set(v___x_4132_, 1, v___x_4137_);
                    lean_ctor_set(v___x_4132_, 0, v_outLevelParams_4136_);
                    v___x_4139_ = v___x_4132_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4141_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_outLevelParams_4136_);
                    lean_ctor_set(v_reuseFailAlloc_4141_, 1, v___x_4137_);
                    v___x_4139_ = v_reuseFailAlloc_4141_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_as_x27_4123_ = v_tail_4128_;
                v_b_4124_ = v___x_4139_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4___redArg___boxed(
    mut v___x_4145_: *mut LeanObject,
    mut v_as_x27_4146_: *mut LeanObject,
    mut v_b_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4149_: *mut LeanObject = core::ptr::null_mut();
    v_res_4149_ = l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4___redArg(v___x_4145_, v_as_x27_4146_, v_b_4147_);
    lean_dec(v_as_x27_4146_);
    lean_dec_ref(v___x_4145_);
    return v_res_4149_;
}
pub unsafe fn l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(
    mut v_a_4150_: *mut LeanObject,
    mut v_x_4151_: *mut LeanObject,
) -> u8 {
    let mut v___x_4152_: u8 = 0;
    let mut v_head_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4151_) == 0 {
                    v___x_4152_ = 0;
                    return v___x_4152_;
                } else {
                    v_head_4153_ = lean_ctor_get(v_x_4151_, 0);
                    v_tail_4154_ = lean_ctor_get(v_x_4151_, 1);
                    v___x_4155_ = lean_name_eq(v_a_4150_, v_head_4153_);
                    if v___x_4155_ == 0 {
                        v_x_4151_ = v_tail_4154_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4155_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1___boxed(
    mut v_a_4157_: *mut LeanObject,
    mut v_x_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4159_: u8 = 0;
    let mut v_r_4160_: *mut LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v_a_4157_, v_x_4158_);
    lean_dec(v_x_4158_);
    lean_dec(v_a_4157_);
    v_r_4160_ = lean_box((v_res_4159_) as usize);
    return v_r_4160_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    v___x_4162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__0;
    v___x_4163_ = l_Lean_stringToMessageData(v___x_4162_);
    return v___x_4163_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5(
    mut v___x_4164_: *mut LeanObject,
    mut v_decl_4165_: *mut LeanObject,
    mut v_as_4166_: *mut LeanObject,
    mut v_i_4167_: usize,
    mut v_stop_4168_: usize,
    mut v_b_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: usize = 0;
    let mut v___x_4176_: usize = 0;
    let mut v___x_4178_: u8 = 0;
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4178_ = lean_usize_dec_eq(v_i_4167_, v_stop_4168_);
                if v___x_4178_ == 0 {
                    v___x_4179_ = lean_array_uget_borrowed(v_as_4166_, v_i_4167_);
                    v___x_4180_ = l_Lean_Syntax_getId(v___x_4179_);
                    v___x_4181_ = l_List_elem___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__1(v___x_4180_, v___x_4164_);
                    lean_dec(v___x_4180_);
                    if v___x_4181_ == 0 {
                        v___x_4182_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg___closed__5);
                        lean_inc(v___x_4179_);
                        v___x_4183_ = l_Lean_MessageData_ofSyntax(v___x_4179_);
                        v___x_4184_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4184_, 0, v___x_4182_);
                        lean_ctor_set(v___x_4184_, 1, v___x_4183_);
                        v___x_4185_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___closed__1);
                        v___x_4186_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4186_, 0, v___x_4184_);
                        lean_ctor_set(v___x_4186_, 1, v___x_4185_);
                        lean_inc(v_decl_4165_);
                        v___x_4187_ = l_Lean_MessageData_ofName(v_decl_4165_);
                        v___x_4188_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4188_, 0, v___x_4186_);
                        lean_ctor_set(v___x_4188_, 1, v___x_4187_);
                        v___x_4189_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4189_, 0, v___x_4188_);
                        lean_ctor_set(v___x_4189_, 1, v___x_4182_);
                        v___x_4190_ = l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2___redArg(v___x_4179_, v___x_4189_, v___y_4170_, v___y_4171_);
                        if lean_obj_tag(v___x_4190_) == 0 {
                            v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
                            lean_inc(v_a_4191_);
                            lean_dec_ref_known(v___x_4190_, 1);
                            v_a_4174_ = v_a_4191_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_decl_4165_);
                            return v___x_4190_;
                        }
                    } else {
                        v___x_4192_ = lean_box(0);
                        v_a_4174_ = v___x_4192_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_decl_4165_);
                    v___x_4193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4193_, 0, v_b_4169_);
                    return v___x_4193_;
                }
            }
            1 => {
                v___x_4175_ = 1usize;
                v___x_4176_ = lean_usize_add(v_i_4167_, v___x_4175_);
                v_i_4167_ = v___x_4176_;
                v_b_4169_ = v_a_4174_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5___boxed(
    mut v___x_4194_: *mut LeanObject,
    mut v_decl_4195_: *mut LeanObject,
    mut v_as_4196_: *mut LeanObject,
    mut v_i_4197_: *mut LeanObject,
    mut v_stop_4198_: *mut LeanObject,
    mut v_b_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4203_: usize = 0;
    let mut v_stop_boxed_4204_: usize = 0;
    let mut v_res_4205_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4203_ = lean_unbox_usize(v_i_4197_);
    lean_dec(v_i_4197_);
    v_stop_boxed_4204_ = lean_unbox_usize(v_stop_4198_);
    lean_dec(v_stop_4198_);
    v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5(v___x_4194_, v_decl_4195_, v_as_4196_, v_i_boxed_4203_, v_stop_boxed_4204_, v_b_4199_, v___y_4200_, v___y_4201_);
    lean_dec(v___y_4201_);
    lean_dec_ref(v___y_4200_);
    lean_dec_ref(v_as_4196_);
    lean_dec(v___x_4194_);
    return v_res_4205_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    v___x_4207_ = l___private_Lean_Class_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_;
    v___x_4208_ = l_Lean_stringToMessageData(v___x_4207_);
    return v___x_4208_;
}
pub unsafe fn _init_l___private_Lean_Class_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    v___x_4210_ = l___private_Lean_Class_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_;
    v___x_4211_ = l_Lean_stringToMessageData(v___x_4210_);
    return v___x_4211_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn___lam__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_(
    mut v___x_4212_: *mut LeanObject,
    mut v_i_4213_: *mut LeanObject,
    mut v___x_4214_: *mut LeanObject,
    mut v_decl_4215_: *mut LeanObject,
    mut v_stx_4216_: *mut LeanObject,
    mut v_kind_4217_: u8,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4236_: u8 = 0;
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4249_: u8 = 0;
    let mut v_unused_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4257_: usize = 0;
    let mut v___x_4258_: usize = 0;
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: usize = 0;
    let mut v___x_4289_: usize = 0;
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: usize = 0;
    let mut v___x_4292_: usize = 0;
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: u8 = 0;
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: u8 = 0;
    let mut v___x_4313_: u8 = 0;
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4312_ = 0;
                v___x_4313_ = l_Lean_instBEqAttributeKind_beq(v_kind_4217_, v___x_4312_);
                if v___x_4313_ == 0 {
                    lean_dec(v_decl_4215_);
                    lean_dec(v_i_4213_);
                    lean_dec(v___x_4212_);
                    v___x_4314_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Class_0__Lean_init_spec__3___redArg(v___x_4214_, v_kind_4217_, v___y_4218_, v___y_4219_);
                    return v___x_4314_;
                } else {
                    lean_dec(v___x_4214_);
                    state = 9;
                    continue;
                }
            }
            1 => {
                v___x_4225_ = lean_st_ref_take(v___y_4223_);
                v_env_4226_ = lean_ctor_get(v___x_4225_, 0);
                v_nextMacroScope_4227_ = lean_ctor_get(v___x_4225_, 1);
                v_ngen_4228_ = lean_ctor_get(v___x_4225_, 2);
                v_auxDeclNGen_4229_ = lean_ctor_get(v___x_4225_, 3);
                v_traceState_4230_ = lean_ctor_get(v___x_4225_, 4);
                v_messages_4231_ = lean_ctor_get(v___x_4225_, 6);
                v_infoState_4232_ = lean_ctor_get(v___x_4225_, 7);
                v_snapshotTasks_4233_ = lean_ctor_get(v___x_4225_, 8);
                v_isSharedCheck_4249_ = (!lean_is_exclusive(v___x_4225_)) as u8;
                if v_isSharedCheck_4249_ == 0 {
                    v_unused_4250_ = lean_ctor_get(v___x_4225_, 5);
                    lean_dec(v_unused_4250_);
                    v___x_4235_ = v___x_4225_;
                    v_isShared_4236_ = v_isSharedCheck_4249_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4233_);
                    lean_inc(v_infoState_4232_);
                    lean_inc(v_messages_4231_);
                    lean_inc(v_traceState_4230_);
                    lean_inc(v_auxDeclNGen_4229_);
                    lean_inc(v_ngen_4228_);
                    lean_inc(v_nextMacroScope_4227_);
                    lean_inc(v_env_4226_);
                    lean_dec(v___x_4225_);
                    v___x_4235_ = lean_box(0);
                    v_isShared_4236_ = v_isSharedCheck_4249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4237_ = l_Lean_classExtension;
                v_toEnvExtension_4238_ = lean_ctor_get(v___x_4237_, 0);
                v_asyncMode_4239_ = lean_ctor_get(v_toEnvExtension_4238_, 2);
                v___x_4240_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4240_, 0, v_decl_4215_);
                lean_ctor_set(v___x_4240_, 1, v___y_4224_);
                lean_ctor_set(v___x_4240_, 2, v___y_4222_);
                v___x_4241_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4237_,
                    v_env_4226_,
                    v___x_4240_,
                    v_asyncMode_4239_,
                    v___x_4212_,
                );
                v___x_4242_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2_once), _init_l_Lean_setEnv___at___00__private_Lean_Class_0__Lean_init_spec__2___redArg___closed__2);
                if v_isShared_4236_ == 0 {
                    lean_ctor_set(v___x_4235_, 5, v___x_4242_);
                    lean_ctor_set(v___x_4235_, 0, v___x_4241_);
                    v___x_4244_ = v___x_4235_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4241_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_nextMacroScope_4227_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 2, v_ngen_4228_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 3, v_auxDeclNGen_4229_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 4, v_traceState_4230_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 5, v___x_4242_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 6, v_messages_4231_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 7, v_infoState_4232_);
                    lean_ctor_set(v_reuseFailAlloc_4248_, 8, v_snapshotTasks_4233_);
                    v___x_4244_ = v_reuseFailAlloc_4248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4245_ = lean_st_ref_set(v___y_4223_, v___x_4244_);
                v___x_4246_ = lean_box(0);
                v___x_4247_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4247_, 0, v___x_4246_);
                return v___x_4247_;
            }
            4 => {
                v_sz_4257_ = lean_array_size(v___y_4252_);
                v___x_4258_ = 0usize;
                v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__3(v_sz_4257_, v___x_4258_, v___y_4252_);
                v___x_4260_ = lean_mk_empty_array_with_capacity(v_i_4213_);
                lean_inc_ref(v___x_4260_);
                v___x_4261_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4261_, 0, v___x_4260_);
                lean_ctor_set(v___x_4261_, 1, v_i_4213_);
                v___x_4262_ = l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4___redArg(v___x_4259_, v___y_4253_, v___x_4261_);
                lean_dec(v___y_4253_);
                lean_dec_ref(v___x_4259_);
                v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
                lean_inc(v_a_4263_);
                lean_dec_ref(v___x_4262_);
                v_fst_4264_ = lean_ctor_get(v_a_4263_, 0);
                lean_inc(v_fst_4264_);
                lean_dec(v_a_4263_);
                v___x_4265_ = l_Lean_getOutParamPositions_x3f(v___y_4254_, v_decl_4215_);
                if lean_obj_tag(v___x_4265_) == 0 {
                    v___y_4222_ = v_fst_4264_;
                    v___y_4223_ = v___y_4255_;
                    v___y_4224_ = v___x_4260_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_4260_);
                    v_val_4266_ = lean_ctor_get(v___x_4265_, 0);
                    lean_inc(v_val_4266_);
                    lean_dec_ref_known(v___x_4265_, 1);
                    v___y_4222_ = v_fst_4264_;
                    v___y_4223_ = v___y_4255_;
                    v___y_4224_ = v_val_4266_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if lean_obj_tag(v___y_4273_) == 0 {
                    lean_dec_ref_known(v___y_4273_, 1);
                    v___y_4252_ = v___y_4268_;
                    v___y_4253_ = v___y_4269_;
                    v___y_4254_ = v___y_4272_;
                    v___y_4255_ = v___y_4271_;
                    v___y_4256_ = v___y_4270_;
                    state = 4;
                    continue;
                } else {
                    lean_dec_ref(v___y_4272_);
                    lean_dec(v___y_4269_);
                    lean_dec_ref(v___y_4268_);
                    lean_dec(v_decl_4215_);
                    lean_dec(v_i_4213_);
                    lean_dec(v___x_4212_);
                    return v___y_4273_;
                }
            }
            6 => {
                lean_inc(v_decl_4215_);
                v___x_4278_ = l_Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0(v_decl_4215_, v___y_4276_, v___y_4277_);
                if lean_obj_tag(v___x_4278_) == 0 {
                    v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
                    lean_inc(v_a_4279_);
                    lean_dec_ref_known(v___x_4278_, 1);
                    v___x_4280_ = l_Lean_ConstantInfo_levelParams(v_a_4279_);
                    lean_dec(v_a_4279_);
                    v___x_4281_ = lean_unsigned_to_nat(1);
                    v___x_4282_ = l_Lean_Syntax_getArg(v_stx_4216_, v___x_4281_);
                    v___x_4283_ = l_Lean_Syntax_getArgs(v___x_4282_);
                    lean_dec(v___x_4282_);
                    v___x_4284_ = lean_array_get_size(v___x_4283_);
                    v___x_4285_ = lean_nat_dec_lt(v_i_4213_, v___x_4284_);
                    if v___x_4285_ == 0 {
                        v___y_4252_ = v___x_4283_;
                        v___y_4253_ = v___x_4280_;
                        v___y_4254_ = v___y_4275_;
                        v___y_4255_ = v___y_4277_;
                        v___y_4256_ = v___y_4276_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4286_ = lean_box(0);
                        v___x_4287_ = lean_nat_dec_le(v___x_4284_, v___x_4284_);
                        if v___x_4287_ == 0 {
                            if v___x_4285_ == 0 {
                                v___y_4252_ = v___x_4283_;
                                v___y_4253_ = v___x_4280_;
                                v___y_4254_ = v___y_4275_;
                                v___y_4255_ = v___y_4277_;
                                v___y_4256_ = v___y_4276_;
                                state = 4;
                                continue;
                            } else {
                                v___x_4288_ = 0usize;
                                v___x_4289_ = lean_usize_of_nat(v___x_4284_);
                                lean_inc(v_decl_4215_);
                                v___x_4290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5(v___x_4280_, v_decl_4215_, v___x_4283_, v___x_4288_, v___x_4289_, v___x_4286_, v___y_4276_, v___y_4277_);
                                v___y_4268_ = v___x_4283_;
                                v___y_4269_ = v___x_4280_;
                                v___y_4270_ = v___y_4276_;
                                v___y_4271_ = v___y_4277_;
                                v___y_4272_ = v___y_4275_;
                                v___y_4273_ = v___x_4290_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___x_4291_ = 0usize;
                            v___x_4292_ = lean_usize_of_nat(v___x_4284_);
                            lean_inc(v_decl_4215_);
                            v___x_4293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__5(v___x_4280_, v_decl_4215_, v___x_4283_, v___x_4291_, v___x_4292_, v___x_4286_, v___y_4276_, v___y_4277_);
                            v___y_4268_ = v___x_4283_;
                            v___y_4269_ = v___x_4280_;
                            v___y_4270_ = v___y_4276_;
                            v___y_4271_ = v___y_4277_;
                            v___y_4272_ = v___y_4275_;
                            v___y_4273_ = v___x_4293_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_4275_);
                    lean_dec(v_decl_4215_);
                    lean_dec(v_i_4213_);
                    lean_dec(v___x_4212_);
                    v_a_4294_ = lean_ctor_get(v___x_4278_, 0);
                    v_isSharedCheck_4301_ = (!lean_is_exclusive(v___x_4278_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4296_ = v___x_4278_;
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4294_);
                        lean_dec(v___x_4278_);
                        v___x_4296_ = lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4297_ == 0 {
                    v___x_4299_ = v___x_4296_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
                    v___x_4299_ = v_reuseFailAlloc_4300_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4299_;
            }
            9 => {
                v___x_4303_ = lean_st_ref_get(v___y_4219_);
                v_env_4304_ = lean_ctor_get(v___x_4303_, 0);
                lean_inc_ref_n(v_env_4304_, 2);
                lean_dec(v___x_4303_);
                lean_inc(v_decl_4215_);
                v___x_4305_ = lean_is_class(v_env_4304_, v_decl_4215_);
                if v___x_4305_ == 0 {
                    lean_dec_ref(v_env_4304_);
                    lean_dec(v_i_4213_);
                    lean_dec(v___x_4212_);
                    v___x_4306_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__once), _init_l___private_Lean_Class_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_);
                    v___x_4307_ = l_Lean_MessageData_ofName(v_decl_4215_);
                    v___x_4308_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4308_, 0, v___x_4306_);
                    lean_ctor_set(v___x_4308_, 1, v___x_4307_);
                    v___x_4309_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__once), _init_l___private_Lean_Class_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_);
                    v___x_4310_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4310_, 0, v___x_4308_);
                    lean_ctor_set(v___x_4310_, 1, v___x_4309_);
                    v___x_4311_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(v___x_4310_, v___y_4218_, v___y_4219_);
                    return v___x_4311_;
                } else {
                    v___y_4275_ = v_env_4304_;
                    v___y_4276_ = v___y_4218_;
                    v___y_4277_ = v___y_4219_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn___lam__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2____boxed(
    mut v___x_4315_: *mut LeanObject,
    mut v_i_4316_: *mut LeanObject,
    mut v___x_4317_: *mut LeanObject,
    mut v_decl_4318_: *mut LeanObject,
    mut v_stx_4319_: *mut LeanObject,
    mut v_kind_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_4324_: u8 = 0;
    let mut v_res_4325_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_4324_ = (lean_unbox(v_kind_4320_) as u8);
    v_res_4325_ = l___private_Lean_Class_0__Lean_initFn___lam__0_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_(v___x_4315_, v_i_4316_, v___x_4317_, v_decl_4318_, v_stx_4319_, v_kind_boxed_4324_, v___y_4321_, v___y_4322_);
    lean_dec(v___y_4322_);
    lean_dec_ref(v___y_4321_);
    lean_dec(v_stx_4319_);
    return v_res_4325_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_(
    mut v___x_4326_: *mut LeanObject,
    mut v_decl_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    v___x_4331_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__1),
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__1_once),
        _init_l___private_Lean_Class_0__Lean_init___lam__1___closed__1,
    );
    v___x_4332_ = l_Lean_MessageData_ofName(v___x_4326_);
    v___x_4333_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4333_, 0, v___x_4331_);
    lean_ctor_set(v___x_4333_, 1, v___x_4332_);
    v___x_4334_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__3),
        core::ptr::addr_of_mut!(l___private_Lean_Class_0__Lean_init___lam__1___closed__3_once),
        _init_l___private_Lean_Class_0__Lean_init___lam__1___closed__3,
    );
    v___x_4335_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4335_, 0, v___x_4333_);
    lean_ctor_set(v___x_4335_, 1, v___x_4334_);
    v___x_4336_ = l_Lean_throwError___at___00__private_Lean_Class_0__Lean_init_spec__0___redArg(
        v___x_4335_,
        v___y_4328_,
        v___y_4329_,
    );
    return v___x_4336_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2____boxed(
    mut v___x_4337_: *mut LeanObject,
    mut v_decl_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4342_: *mut LeanObject = core::ptr::null_mut();
    v_res_4342_ = l___private_Lean_Class_0__Lean_initFn___lam__1_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_(v___x_4337_, v_decl_4338_, v___y_4339_, v___y_4340_);
    lean_dec(v___y_4340_);
    lean_dec_ref(v___y_4339_);
    lean_dec(v_decl_4338_);
    return v_res_4342_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    v___x_4391_ = l___private_Lean_Class_0__Lean_initFn___closed__18_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_;
    v___x_4392_ = l_Lean_registerBuiltinAttribute(v___x_4391_);
    return v___x_4392_;
}
pub unsafe fn l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2____boxed(
    mut v_a_4393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4394_: *mut LeanObject = core::ptr::null_mut();
    v_res_4394_ =
        l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_();
    return v_res_4394_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2(
    mut v_00_u03b1_4395_: *mut LeanObject,
    mut v_ref_4396_: *mut LeanObject,
    mut v_msg_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    v___x_4401_ = l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2___redArg(v_ref_4396_, v_msg_4397_, v___y_4398_, v___y_4399_);
    return v___x_4401_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2___boxed(
    mut v_00_u03b1_4402_: *mut LeanObject,
    mut v_ref_4403_: *mut LeanObject,
    mut v_msg_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4408_: *mut LeanObject = core::ptr::null_mut();
    v_res_4408_ = l_Lean_throwErrorAt___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__2(v_00_u03b1_4402_, v_ref_4403_, v_msg_4404_, v___y_4405_, v___y_4406_);
    lean_dec(v___y_4406_);
    lean_dec_ref(v___y_4405_);
    lean_dec(v_ref_4403_);
    return v_res_4408_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4(
    mut v___x_4409_: *mut LeanObject,
    mut v_as_4410_: *mut LeanObject,
    mut v_as_x27_4411_: *mut LeanObject,
    mut v_b_4412_: *mut LeanObject,
    mut v_a_4413_: *mut LeanObject,
    mut v___y_4414_: *mut LeanObject,
    mut v___y_4415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    v___x_4417_ = l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4___redArg(v___x_4409_, v_as_x27_4411_, v_b_4412_);
    return v___x_4417_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4___boxed(
    mut v___x_4418_: *mut LeanObject,
    mut v_as_4419_: *mut LeanObject,
    mut v_as_x27_4420_: *mut LeanObject,
    mut v_b_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
    mut v___y_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
    mut v___y_4425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4426_: *mut LeanObject = core::ptr::null_mut();
    v_res_4426_ = l_List_forIn_x27_loop___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__4(v___x_4418_, v_as_4419_, v_as_x27_4420_, v_b_4421_, v_a_4422_, v___y_4423_, v___y_4424_);
    lean_dec(v___y_4424_);
    lean_dec_ref(v___y_4423_);
    lean_dec(v_as_x27_4420_);
    lean_dec(v_as_4419_);
    lean_dec_ref(v___x_4418_);
    return v_res_4426_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_4427_: *mut LeanObject,
    mut v_constName_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    v___x_4432_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_4428_, v___y_4429_, v___y_4430_);
    return v___x_4432_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_4433_: *mut LeanObject,
    mut v_constName_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4438_: *mut LeanObject = core::ptr::null_mut();
    v_res_4438_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_4433_, v_constName_4434_, v___y_4435_, v___y_4436_);
    lean_dec(v___y_4436_);
    lean_dec_ref(v___y_4435_);
    return v_res_4438_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b1_4439_: *mut LeanObject,
    mut v_ref_4440_: *mut LeanObject,
    mut v_constName_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    v___x_4445_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_4440_, v_constName_4441_, v___y_4442_, v___y_4443_);
    return v___x_4445_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4446_: *mut LeanObject,
    mut v_ref_4447_: *mut LeanObject,
    mut v_constName_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4452_: *mut LeanObject = core::ptr::null_mut();
    v_res_4452_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_4446_, v_ref_4447_, v_constName_4448_, v___y_4449_, v___y_4450_);
    lean_dec(v___y_4450_);
    lean_dec_ref(v___y_4449_);
    lean_dec(v_ref_4447_);
    return v_res_4452_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7(
    mut v_00_u03b1_4453_: *mut LeanObject,
    mut v_ref_4454_: *mut LeanObject,
    mut v_msg_4455_: *mut LeanObject,
    mut v_declHint_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    v___x_4460_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7___redArg(v_ref_4454_, v_msg_4455_, v_declHint_4456_, v___y_4457_, v___y_4458_);
    return v___x_4460_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7___boxed(
    mut v_00_u03b1_4461_: *mut LeanObject,
    mut v_ref_4462_: *mut LeanObject,
    mut v_msg_4463_: *mut LeanObject,
    mut v_declHint_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
    mut v___y_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4468_: *mut LeanObject = core::ptr::null_mut();
    v_res_4468_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7(v_00_u03b1_4461_, v_ref_4462_, v_msg_4463_, v_declHint_4464_, v___y_4465_, v___y_4466_);
    lean_dec(v___y_4466_);
    lean_dec_ref(v___y_4465_);
    lean_dec(v_ref_4462_);
    return v_res_4468_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(
    mut v_msg_4469_: *mut LeanObject,
    mut v_declHint_4470_: *mut LeanObject,
    mut v___y_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    v___x_4474_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___redArg(v_msg_4469_, v_declHint_4470_, v___y_4472_);
    return v___x_4474_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9___boxed(
    mut v_msg_4475_: *mut LeanObject,
    mut v_declHint_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4480_: *mut LeanObject = core::ptr::null_mut();
    v_res_4480_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__7_spec__8_spec__9(v_msg_4475_, v_declHint_4476_, v___y_4477_, v___y_4478_);
    lean_dec(v___y_4478_);
    lean_dec_ref(v___y_4477_);
    return v_res_4480_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Class(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedClassState_default = _init_l_Lean_instInhabitedClassState_default();
    lean_mark_persistent(l_Lean_instInhabitedClassState_default);
    l_Lean_instInhabitedClassState = _init_l_Lean_instInhabitedClassState();
    lean_mark_persistent(l_Lean_instInhabitedClassState);
    res = l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_903839608____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_classExtension = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_classExtension);
    lean_dec_ref(res);
    res = l___private_Lean_Class_0__Lean_init();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Class_0__Lean_init___regBuiltin___private_Lean_Class_0__Lean_init_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Class_0__Lean_initFn_00___x40_Lean_Class_1274053790____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Class(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Class(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_CollectLevelParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Class(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Class(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Class(builtin);
}
