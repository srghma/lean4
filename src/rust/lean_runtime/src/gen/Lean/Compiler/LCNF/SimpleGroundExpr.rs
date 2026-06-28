// Lean compiler output
// Module: Lean.Compiler.LCNF.SimpleGroundExpr
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PassManager Init.While
use crate::r#gen::Init::Data::Array::Basic::l_Array_reverse___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_CtorInfo_isScalar;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, l_Lean_Compiler_LCNF_getPurity___redArg,
    runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instBEqFVarId_beq___boxed, l_Lean_instHashableFVarId_hash,
    l_Lean_instHashableFVarId_hash___boxed,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::l_Std_DHashMap_Internal_Raw_u2080_insert___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint16_shift_right, lean_uint32_shift_right, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint16_to_nat, lean_uint16_to_uint8, lean_uint32_to_uint8,
    lean_uint64_to_uint8, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mod, lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_uint8_of_nat, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_box_uint32, lean_box_uint64, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint16, lean_ctor_get_uint32,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint16, lean_ctor_set_uint32, lean_ctor_set_uint64,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
pub static l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default___closed__0_value
)
    as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__1_value:
    LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__1_value
)
    as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__1_value
)
    as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default___closed__1_value
)
    as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 0]};
static mut l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__0_value) as *mut LeanObject;
pub static l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0]};
static mut l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 97, 112, 0]};
static mut l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedSimpleGroundValue_default___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundValue_default___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundValue_default___closed__0_value
) as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_instInhabitedSimpleGroundValue_default: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundValue_default___closed__0_value
)
    as *mut LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_instInhabitedSimpleGroundValue: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSimpleGroundValue_default___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedSimpleGroundArg_default___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqFVarId_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableFVarId_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [78, 97, 109, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [95, 111, 118, 101, 114, 114, 105, 100, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__9_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 49, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__10_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 50, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__11_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 51, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 52, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__13_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 53, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__14_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 54, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 55, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__16_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 107, 83, 116, 114, 56, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__17_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__18_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [66, 121, 116, 101, 65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__19_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__20_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 107, 69, 109, 112, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__21_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 109, 112, 116, 121, 87, 105, 116, 104, 67, 97, 112, 97, 99, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__22_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 117, 115, 104, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 103, 103, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___boxed__const__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut LeanObject] };
pub static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___boxed__const__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___boxed__const__1_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__3: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__4_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 105, 109, 112, 108, 101, 71, 114, 111, 117, 110, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__4_value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__3_value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__4_value) as *mut LeanObject,15567172459987332627 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__6_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__9_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [77, 97, 114, 107, 101, 100, 32, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__11_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [32, 97, 115, 32, 115, 105, 109, 112, 108, 101, 32, 103, 114, 111, 117, 110, 100, 32, 101, 120, 112, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_detectSimpleGround___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Compiler_LCNF_detectSimpleGround___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_LCNF_detectSimpleGround___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_detectSimpleGround___closed__1_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            100, 101, 116, 101, 99, 116, 83, 105, 109, 112, 108, 101, 71, 114, 111, 117, 110, 100,
            0,
        ],
    };
static mut l_Lean_Compiler_LCNF_detectSimpleGround___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_detectSimpleGround___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__1_value)
                as *mut LeanObject,
            15164016850214686516 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_detectSimpleGround___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_detectSimpleGround___closed__3_value: LeanCtorObject<4> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__0_value)
                as *mut LeanObject,
            514 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_detectSimpleGround___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_detectSimpleGround: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_detectSimpleGround___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__3_value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 105, 109, 112, 108, 101, 71, 114, 111, 117, 110, 100, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,5952041526617687869 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,3197087447850422216 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4_value) as *mut LeanObject,15945181512546640033 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__3_value) as *mut LeanObject,15619452550673981903 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,6933882419195184034 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,3697391375259220503 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,16145185111338127058 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4_value) as *mut LeanObject,13188025159061354707 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__3_value) as *mut LeanObject,578058697545099957 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,4583063848735246688 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,12534709594395342888 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,((( 1728217338 as usize) << 1) | 1) as *mut LeanObject,643826057143225140 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,8491443248124707643 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,14878447190128046491 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,736030353716638958 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_ctorIdx(
    mut v_x_3445_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3445_) {
        0 => {
            let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
            v___x_3446_ = lean_unsigned_to_nat(0);
            return v___x_3446_;
        }
        1 => {
            let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
            v___x_3447_ = lean_unsigned_to_nat(1);
            return v___x_3447_;
        }
        _ => {
            let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
            v___x_3448_ = lean_unsigned_to_nat(2);
            return v___x_3448_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_ctorIdx___boxed(
    mut v_x_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3450_: *mut LeanObject = core::ptr::null_mut();
    v_res_3450_ = l_Lean_Compiler_LCNF_SimpleGroundArg_ctorIdx(v_x_3449_);
    lean_dec_ref(v_x_3449_);
    return v_res_3450_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(
    mut v_t_3451_: *mut LeanObject,
    mut v_k_3452_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_3451_) == 2 {
        let mut v_s_3453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
        v_s_3453_ = lean_ctor_get(v_t_3451_, 0);
        lean_inc_ref(v_s_3453_);
        lean_dec_ref_known(v_t_3451_, 1);
        v___x_3454_ = lean_apply_1(v_k_3452_, v_s_3453_);
        return v___x_3454_;
    } else {
        let mut v_val_3455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
        v_val_3455_ = lean_ctor_get(v_t_3451_, 0);
        lean_inc(v_val_3455_);
        lean_dec_ref(v_t_3451_);
        v___x_3456_ = lean_apply_1(v_k_3452_, v_val_3455_);
        return v___x_3456_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim(
    mut v_motive_3457_: *mut LeanObject,
    mut v_ctorIdx_3458_: *mut LeanObject,
    mut v_t_3459_: *mut LeanObject,
    mut v_h_3460_: *mut LeanObject,
    mut v_k_3461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    v___x_3462_ = l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(v_t_3459_, v_k_3461_);
    return v___x_3462_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___boxed(
    mut v_motive_3463_: *mut LeanObject,
    mut v_ctorIdx_3464_: *mut LeanObject,
    mut v_t_3465_: *mut LeanObject,
    mut v_h_3466_: *mut LeanObject,
    mut v_k_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim(
        v_motive_3463_,
        v_ctorIdx_3464_,
        v_t_3465_,
        v_h_3466_,
        v_k_3467_,
    );
    lean_dec(v_ctorIdx_3464_);
    return v_res_3468_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_tagged_elim___redArg(
    mut v_t_3469_: *mut LeanObject,
    mut v_tagged_3470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    v___x_3471_ = l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(v_t_3469_, v_tagged_3470_);
    return v___x_3471_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_tagged_elim(
    mut v_motive_3472_: *mut LeanObject,
    mut v_t_3473_: *mut LeanObject,
    mut v_h_3474_: *mut LeanObject,
    mut v_tagged_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    v___x_3476_ = l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(v_t_3473_, v_tagged_3475_);
    return v___x_3476_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_reference_elim___redArg(
    mut v_t_3477_: *mut LeanObject,
    mut v_reference_3478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    v___x_3479_ =
        l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(v_t_3477_, v_reference_3478_);
    return v___x_3479_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_reference_elim(
    mut v_motive_3480_: *mut LeanObject,
    mut v_t_3481_: *mut LeanObject,
    mut v_h_3482_: *mut LeanObject,
    mut v_reference_3483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ =
        l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(v_t_3481_, v_reference_3483_);
    return v___x_3484_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_rawReference_elim___redArg(
    mut v_t_3485_: *mut LeanObject,
    mut v_rawReference_3486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3487_ =
        l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(v_t_3485_, v_rawReference_3486_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundArg_rawReference_elim(
    mut v_motive_3488_: *mut LeanObject,
    mut v_t_3489_: *mut LeanObject,
    mut v_h_3490_: *mut LeanObject,
    mut v_rawReference_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_3492_ =
        l_Lean_Compiler_LCNF_SimpleGroundArg_ctorElim___redArg(v_t_3489_, v_rawReference_3491_);
    return v___x_3492_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorIdx(
    mut v_x_3497_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3497_) {
        0 => {
            let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
            v___x_3498_ = lean_unsigned_to_nat(0);
            return v___x_3498_;
        }
        1 => {
            let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
            v___x_3499_ = lean_unsigned_to_nat(1);
            return v___x_3499_;
        }
        2 => {
            let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
            v___x_3500_ = lean_unsigned_to_nat(2);
            return v___x_3500_;
        }
        3 => {
            let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
            v___x_3501_ = lean_unsigned_to_nat(3);
            return v___x_3501_;
        }
        4 => {
            let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
            v___x_3502_ = lean_unsigned_to_nat(4);
            return v___x_3502_;
        }
        5 => {
            let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
            v___x_3503_ = lean_unsigned_to_nat(5);
            return v___x_3503_;
        }
        _ => {
            let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
            v___x_3504_ = lean_unsigned_to_nat(6);
            return v___x_3504_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorIdx___boxed(
    mut v_x_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3506_: *mut LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorIdx(v_x_3505_);
    lean_dec_ref(v_x_3505_);
    return v_res_3506_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(
    mut v_t_3507_: *mut LeanObject,
    mut v_k_3508_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_3507_) {
        0 => {
            let mut v_cidx_3509_: *mut LeanObject = core::ptr::null_mut();
            let mut v_objArgs_3510_: *mut LeanObject = core::ptr::null_mut();
            let mut v_usizeArgs_3511_: *mut LeanObject = core::ptr::null_mut();
            let mut v_scalarArgs_3512_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
            v_cidx_3509_ = lean_ctor_get(v_t_3507_, 0);
            lean_inc(v_cidx_3509_);
            v_objArgs_3510_ = lean_ctor_get(v_t_3507_, 1);
            lean_inc_ref(v_objArgs_3510_);
            v_usizeArgs_3511_ = lean_ctor_get(v_t_3507_, 2);
            lean_inc_ref(v_usizeArgs_3511_);
            v_scalarArgs_3512_ = lean_ctor_get(v_t_3507_, 3);
            lean_inc_ref(v_scalarArgs_3512_);
            lean_dec_ref_known(v_t_3507_, 4);
            v___x_3513_ = lean_apply_4(
                v_k_3508_,
                v_cidx_3509_,
                v_objArgs_3510_,
                v_usizeArgs_3511_,
                v_scalarArgs_3512_,
            );
            return v___x_3513_;
        }
        2 => {
            let mut v_func_3514_: *mut LeanObject = core::ptr::null_mut();
            let mut v_args_3515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
            v_func_3514_ = lean_ctor_get(v_t_3507_, 0);
            lean_inc(v_func_3514_);
            v_args_3515_ = lean_ctor_get(v_t_3507_, 1);
            lean_inc_ref(v_args_3515_);
            lean_dec_ref_known(v_t_3507_, 2);
            v___x_3516_ = lean_apply_2(v_k_3508_, v_func_3514_, v_args_3515_);
            return v___x_3516_;
        }
        4 => {
            let mut v_n_3517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
            v_n_3517_ = lean_ctor_get(v_t_3507_, 0);
            lean_inc(v_n_3517_);
            lean_dec_ref_known(v_t_3507_, 1);
            v___x_3518_ = lean_apply_1(v_k_3508_, v_n_3517_);
            return v___x_3518_;
        }
        _ => {
            let mut v_data_3519_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
            v_data_3519_ = lean_ctor_get(v_t_3507_, 0);
            lean_inc_ref(v_data_3519_);
            lean_dec_ref(v_t_3507_);
            v___x_3520_ = lean_apply_1(v_k_3508_, v_data_3519_);
            return v___x_3520_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim(
    mut v_motive_3521_: *mut LeanObject,
    mut v_ctorIdx_3522_: *mut LeanObject,
    mut v_t_3523_: *mut LeanObject,
    mut v_h_3524_: *mut LeanObject,
    mut v_k_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3523_, v_k_3525_);
    return v___x_3526_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___boxed(
    mut v_motive_3527_: *mut LeanObject,
    mut v_ctorIdx_3528_: *mut LeanObject,
    mut v_t_3529_: *mut LeanObject,
    mut v_h_3530_: *mut LeanObject,
    mut v_k_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3532_: *mut LeanObject = core::ptr::null_mut();
    v_res_3532_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim(
        v_motive_3527_,
        v_ctorIdx_3528_,
        v_t_3529_,
        v_h_3530_,
        v_k_3531_,
    );
    lean_dec(v_ctorIdx_3528_);
    return v_res_3532_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_ctor_elim___redArg(
    mut v_t_3533_: *mut LeanObject,
    mut v_ctor_3534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    v___x_3535_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3533_, v_ctor_3534_);
    return v___x_3535_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_ctor_elim(
    mut v_motive_3536_: *mut LeanObject,
    mut v_t_3537_: *mut LeanObject,
    mut v_h_3538_: *mut LeanObject,
    mut v_ctor_3539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3537_, v_ctor_3539_);
    return v___x_3540_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_string_elim___redArg(
    mut v_t_3541_: *mut LeanObject,
    mut v_string_3542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    v___x_3543_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3541_, v_string_3542_);
    return v___x_3543_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_string_elim(
    mut v_motive_3544_: *mut LeanObject,
    mut v_t_3545_: *mut LeanObject,
    mut v_h_3546_: *mut LeanObject,
    mut v_string_3547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    v___x_3548_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3545_, v_string_3547_);
    return v___x_3548_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_pap_elim___redArg(
    mut v_t_3549_: *mut LeanObject,
    mut v_pap_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3549_, v_pap_3550_);
    return v___x_3551_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_pap_elim(
    mut v_motive_3552_: *mut LeanObject,
    mut v_t_3553_: *mut LeanObject,
    mut v_h_3554_: *mut LeanObject,
    mut v_pap_3555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    v___x_3556_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3553_, v_pap_3555_);
    return v___x_3556_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_nameMkStr_elim___redArg(
    mut v_t_3557_: *mut LeanObject,
    mut v_nameMkStr_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    v___x_3559_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3557_, v_nameMkStr_3558_);
    return v___x_3559_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_nameMkStr_elim(
    mut v_motive_3560_: *mut LeanObject,
    mut v_t_3561_: *mut LeanObject,
    mut v_h_3562_: *mut LeanObject,
    mut v_nameMkStr_3563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    v___x_3564_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3561_, v_nameMkStr_3563_);
    return v___x_3564_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_reference_elim___redArg(
    mut v_t_3565_: *mut LeanObject,
    mut v_reference_3566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    v___x_3567_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3565_, v_reference_3566_);
    return v___x_3567_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_reference_elim(
    mut v_motive_3568_: *mut LeanObject,
    mut v_t_3569_: *mut LeanObject,
    mut v_h_3570_: *mut LeanObject,
    mut v_reference_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    v___x_3572_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3569_, v_reference_3571_);
    return v___x_3572_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_array_elim___redArg(
    mut v_t_3573_: *mut LeanObject,
    mut v_array_3574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    v___x_3575_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3573_, v_array_3574_);
    return v___x_3575_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_array_elim(
    mut v_motive_3576_: *mut LeanObject,
    mut v_t_3577_: *mut LeanObject,
    mut v_h_3578_: *mut LeanObject,
    mut v_array_3579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    v___x_3580_ = l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3577_, v_array_3579_);
    return v___x_3580_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_byteArray_elim___redArg(
    mut v_t_3581_: *mut LeanObject,
    mut v_byteArray_3582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    v___x_3583_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3581_, v_byteArray_3582_);
    return v___x_3583_;
}
pub unsafe fn l_Lean_Compiler_LCNF_SimpleGroundExpr_byteArray_elim(
    mut v_motive_3584_: *mut LeanObject,
    mut v_t_3585_: *mut LeanObject,
    mut v_h_3586_: *mut LeanObject,
    mut v_byteArray_3587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    v___x_3588_ =
        l_Lean_Compiler_LCNF_SimpleGroundExpr_ctorElim___redArg(v_t_3585_, v_byteArray_3587_);
    return v___x_3588_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__0()
-> *mut LeanObject {
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3596_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__1()
-> *mut LeanObject {
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    v___x_3597_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__0,
    );
    v___x_3598_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3598_, 0, v___x_3597_);
    return v___x_3598_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2()
-> *mut LeanObject {
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    v___x_3599_ = lean_box(0);
    v___x_3600_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__1,
    );
    v___x_3601_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3601_, 0, v___x_3600_);
    lean_ctor_set(v___x_3601_, 1, v___x_3599_);
    return v___x_3601_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default()
-> *mut LeanObject {
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    v___x_3602_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2,
    );
    return v___x_3602_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState() -> *mut LeanObject {
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default;
    return v___x_3603_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__2(
    mut v_msg_3604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    v___x_3605_ = l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExpr_default;
    v___x_3606_ = lean_panic_fn_borrowed(v___x_3605_, v_msg_3604_);
    return v___x_3606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(
    mut v_keys_3607_: *mut LeanObject,
    mut v_vals_3608_: *mut LeanObject,
    mut v_i_3609_: *mut LeanObject,
    mut v_k_3610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: u8 = 0;
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: u8 = 0;
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3611_ = lean_array_get_size(v_keys_3607_);
                v___x_3612_ = lean_nat_dec_lt(v_i_3609_, v___x_3611_);
                if v___x_3612_ == 0 {
                    lean_dec(v_i_3609_);
                    v___x_3613_ = lean_box(0);
                    return v___x_3613_;
                } else {
                    v_k_x27_3614_ = lean_array_fget_borrowed(v_keys_3607_, v_i_3609_);
                    v___x_3615_ = lean_name_eq(v_k_3610_, v_k_x27_3614_);
                    if v___x_3615_ == 0 {
                        v___x_3616_ = lean_unsigned_to_nat(1);
                        v___x_3617_ = lean_nat_add(v_i_3609_, v___x_3616_);
                        lean_dec(v_i_3609_);
                        v_i_3609_ = v___x_3617_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3619_ = lean_array_fget_borrowed(v_vals_3608_, v_i_3609_);
                        lean_dec(v_i_3609_);
                        lean_inc(v___x_3619_);
                        v___x_3620_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3620_, 0, v___x_3619_);
                        return v___x_3620_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(
    mut v_keys_3621_: *mut LeanObject,
    mut v_vals_3622_: *mut LeanObject,
    mut v_i_3623_: *mut LeanObject,
    mut v_k_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3625_: *mut LeanObject = core::ptr::null_mut();
    v_res_3625_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_3621_, v_vals_3622_, v_i_3623_, v_k_3624_);
    lean_dec(v_k_3624_);
    lean_dec_ref(v_vals_3622_);
    lean_dec_ref(v_keys_3621_);
    return v_res_3625_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_3626_: usize = 0;
    let mut v___x_3627_: usize = 0;
    let mut v___x_3628_: usize = 0;
    v___x_3626_ = 5usize;
    v___x_3627_ = 1usize;
    v___x_3628_ = lean_usize_shift_left(v___x_3627_, v___x_3626_);
    return v___x_3628_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_3629_: usize = 0;
    let mut v___x_3630_: usize = 0;
    let mut v___x_3631_: usize = 0;
    v___x_3629_ = 1usize;
    v___x_3630_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0);
    v___x_3631_ = lean_usize_sub(v___x_3630_, v___x_3629_);
    return v___x_3631_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_x_3632_: *mut LeanObject,
    mut v_x_3633_: usize,
    mut v_x_3634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: usize = 0;
    let mut v___x_3638_: usize = 0;
    let mut v___x_3639_: usize = 0;
    let mut v_j_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: u8 = 0;
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: usize = 0;
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3632_) == 0 {
                    v_es_3635_ = lean_ctor_get(v_x_3632_, 0);
                    v___x_3636_ = lean_box(2);
                    v___x_3637_ = 5usize;
                    v___x_3638_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1);
                    v___x_3639_ = lean_usize_land(v_x_3633_, v___x_3638_);
                    v_j_3640_ = lean_usize_to_nat(v___x_3639_);
                    v___x_3641_ = lean_array_get_borrowed(v___x_3636_, v_es_3635_, v_j_3640_);
                    lean_dec(v_j_3640_);
                    match lean_obj_tag(v___x_3641_) {
                        0 => {
                            v_key_3642_ = lean_ctor_get(v___x_3641_, 0);
                            v_val_3643_ = lean_ctor_get(v___x_3641_, 1);
                            v___x_3644_ = lean_name_eq(v_x_3634_, v_key_3642_);
                            if v___x_3644_ == 0 {
                                v___x_3645_ = lean_box(0);
                                return v___x_3645_;
                            } else {
                                lean_inc(v_val_3643_);
                                v___x_3646_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3646_, 0, v_val_3643_);
                                return v___x_3646_;
                            }
                        }
                        1 => {
                            v_node_3647_ = lean_ctor_get(v___x_3641_, 0);
                            v___x_3648_ = lean_usize_shift_right(v_x_3633_, v___x_3637_);
                            v_x_3632_ = v_node_3647_;
                            v_x_3633_ = v___x_3648_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3650_ = lean_box(0);
                            return v___x_3650_;
                        }
                    }
                } else {
                    v_ks_3651_ = lean_ctor_get(v_x_3632_, 0);
                    v_vs_3652_ = lean_ctor_get(v_x_3632_, 1);
                    v___x_3653_ = lean_unsigned_to_nat(0);
                    v___x_3654_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_ks_3651_, v_vs_3652_, v___x_3653_, v_x_3634_);
                    return v___x_3654_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_x_3655_: *mut LeanObject,
    mut v_x_3656_: *mut LeanObject,
    mut v_x_3657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_568__boxed_3658_: usize = 0;
    let mut v_res_3659_: *mut LeanObject = core::ptr::null_mut();
    v_x_568__boxed_3658_ = lean_unbox_usize(v_x_3656_);
    lean_dec(v_x_3656_);
    v_res_3659_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3655_, v_x_568__boxed_3658_, v_x_3657_);
    lean_dec(v_x_3657_);
    lean_dec_ref(v_x_3655_);
    return v_res_3659_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: u64 = 0;
    v___x_3660_ = lean_unsigned_to_nat(1723);
    v___x_3661_ = lean_uint64_of_nat(v___x_3660_);
    return v___x_3661_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_3662_: *mut LeanObject,
    mut v_x_3663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3665_: u64 = 0;
    let mut v___x_3666_: usize = 0;
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: u64 = 0;
    let mut v_hash_3669_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3663_) == 0 {
                    v___x_3668_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0);
                    v___y_3665_ = v___x_3668_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3669_ = lean_ctor_get_uint64(
                        v_x_3663_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3665_ = v_hash_3669_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3666_ = lean_uint64_to_usize(v___y_3665_);
                v___x_3667_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3662_, v___x_3666_, v_x_3663_);
                return v___x_3667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_3670_: *mut LeanObject,
    mut v_x_3671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3672_: *mut LeanObject = core::ptr::null_mut();
    v_res_3672_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg(v_x_3670_, v_x_3671_);
    lean_dec(v_x_3671_);
    lean_dec_ref(v_x_3670_);
    return v_res_3672_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_x_3673_: *mut LeanObject,
    mut v_x_3674_: *mut LeanObject,
    mut v_x_3675_: *mut LeanObject,
    mut v_x_3676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3681_: u8 = 0;
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: u8 = 0;
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3677_ = lean_ctor_get(v_x_3673_, 0);
                v_vs_3678_ = lean_ctor_get(v_x_3673_, 1);
                v_isSharedCheck_3702_ = (!lean_is_exclusive(v_x_3673_)) as u8;
                if v_isSharedCheck_3702_ == 0 {
                    v___x_3680_ = v_x_3673_;
                    v_isShared_3681_ = v_isSharedCheck_3702_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3678_);
                    lean_inc(v_ks_3677_);
                    lean_dec(v_x_3673_);
                    v___x_3680_ = lean_box(0);
                    v_isShared_3681_ = v_isSharedCheck_3702_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3682_ = lean_array_get_size(v_ks_3677_);
                v___x_3683_ = lean_nat_dec_lt(v_x_3674_, v___x_3682_);
                if v___x_3683_ == 0 {
                    lean_dec(v_x_3674_);
                    v___x_3684_ = lean_array_push(v_ks_3677_, v_x_3675_);
                    v___x_3685_ = lean_array_push(v_vs_3678_, v_x_3676_);
                    if v_isShared_3681_ == 0 {
                        lean_ctor_set(v___x_3680_, 1, v___x_3685_);
                        lean_ctor_set(v___x_3680_, 0, v___x_3684_);
                        v___x_3687_ = v___x_3680_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3684_);
                        lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3685_);
                        v___x_3687_ = v_reuseFailAlloc_3688_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3689_ = lean_array_fget_borrowed(v_ks_3677_, v_x_3674_);
                    v___x_3690_ = lean_name_eq(v_x_3675_, v_k_x27_3689_);
                    if v___x_3690_ == 0 {
                        if v_isShared_3681_ == 0 {
                            v___x_3692_ = v___x_3680_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_ks_3677_);
                            lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_vs_3678_);
                            v___x_3692_ = v_reuseFailAlloc_3696_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3697_ = lean_array_fset(v_ks_3677_, v_x_3674_, v_x_3675_);
                        v___x_3698_ = lean_array_fset(v_vs_3678_, v_x_3674_, v_x_3676_);
                        lean_dec(v_x_3674_);
                        if v_isShared_3681_ == 0 {
                            lean_ctor_set(v___x_3680_, 1, v___x_3698_);
                            lean_ctor_set(v___x_3680_, 0, v___x_3697_);
                            v___x_3700_ = v___x_3680_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3697_);
                            lean_ctor_set(v_reuseFailAlloc_3701_, 1, v___x_3698_);
                            v___x_3700_ = v_reuseFailAlloc_3701_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3687_;
            }
            3 => {
                v___x_3693_ = lean_unsigned_to_nat(1);
                v___x_3694_ = lean_nat_add(v_x_3674_, v___x_3693_);
                lean_dec(v_x_3674_);
                v_x_3673_ = v___x_3692_;
                v_x_3674_ = v___x_3694_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(
    mut v_n_3703_: *mut LeanObject,
    mut v_k_3704_: *mut LeanObject,
    mut v_v_3705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    v___x_3706_ = lean_unsigned_to_nat(0);
    v___x_3707_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_n_3703_, v___x_3706_, v_k_3704_, v_v_3705_);
    return v___x_3707_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    v___x_3708_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3708_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_3709_: *mut LeanObject,
    mut v_x_3710_: usize,
    mut v_x_3711_: usize,
    mut v_x_3712_: *mut LeanObject,
    mut v_x_3713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: usize = 0;
    let mut v___x_3716_: usize = 0;
    let mut v___x_3717_: usize = 0;
    let mut v___x_3718_: usize = 0;
    let mut v_j_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v_v_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_node_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3749_: u8 = 0;
    let mut v___x_3750_: usize = 0;
    let mut v___x_3751_: usize = 0;
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3756_: u8 = 0;
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3758_: u8 = 0;
    let mut v_unused_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3764_: u8 = 0;
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: u8 = 0;
    let mut v_ks_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: usize = 0;
    let mut v___x_3776_: u8 = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: u8 = 0;
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3709_) == 0 {
                    v_es_3714_ = lean_ctor_get(v_x_3709_, 0);
                    v___x_3715_ = 5usize;
                    v___x_3716_ = 1usize;
                    v___x_3717_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1);
                    v___x_3718_ = lean_usize_land(v_x_3710_, v___x_3717_);
                    v_j_3719_ = lean_usize_to_nat(v___x_3718_);
                    v___x_3720_ = lean_array_get_size(v_es_3714_);
                    v___x_3721_ = lean_nat_dec_lt(v_j_3719_, v___x_3720_);
                    if v___x_3721_ == 0 {
                        lean_dec(v_j_3719_);
                        lean_dec(v_x_3713_);
                        lean_dec(v_x_3712_);
                        return v_x_3709_;
                    } else {
                        lean_inc_ref(v_es_3714_);
                        v_isSharedCheck_3758_ = (!lean_is_exclusive(v_x_3709_)) as u8;
                        if v_isSharedCheck_3758_ == 0 {
                            v_unused_3759_ = lean_ctor_get(v_x_3709_, 0);
                            lean_dec(v_unused_3759_);
                            v___x_3723_ = v_x_3709_;
                            v_isShared_3724_ = v_isSharedCheck_3758_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3709_);
                            v___x_3723_ = lean_box(0);
                            v_isShared_3724_ = v_isSharedCheck_3758_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3760_ = lean_ctor_get(v_x_3709_, 0);
                    v_vs_3761_ = lean_ctor_get(v_x_3709_, 1);
                    v_isSharedCheck_3781_ = (!lean_is_exclusive(v_x_3709_)) as u8;
                    if v_isSharedCheck_3781_ == 0 {
                        v___x_3763_ = v_x_3709_;
                        v_isShared_3764_ = v_isSharedCheck_3781_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3761_);
                        lean_inc(v_ks_3760_);
                        lean_dec(v_x_3709_);
                        v___x_3763_ = lean_box(0);
                        v_isShared_3764_ = v_isSharedCheck_3781_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3725_ = lean_array_fget(v_es_3714_, v_j_3719_);
                v___x_3726_ = lean_box(0);
                v_xs_x27_3727_ = lean_array_fset(v_es_3714_, v_j_3719_, v___x_3726_);
                match lean_obj_tag(v_v_3725_) {
                    0 => {
                        v_key_3734_ = lean_ctor_get(v_v_3725_, 0);
                        v_val_3735_ = lean_ctor_get(v_v_3725_, 1);
                        v_isSharedCheck_3745_ = (!lean_is_exclusive(v_v_3725_)) as u8;
                        if v_isSharedCheck_3745_ == 0 {
                            v___x_3737_ = v_v_3725_;
                            v_isShared_3738_ = v_isSharedCheck_3745_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3735_);
                            lean_inc(v_key_3734_);
                            lean_dec(v_v_3725_);
                            v___x_3737_ = lean_box(0);
                            v_isShared_3738_ = v_isSharedCheck_3745_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3746_ = lean_ctor_get(v_v_3725_, 0);
                        v_isSharedCheck_3756_ = (!lean_is_exclusive(v_v_3725_)) as u8;
                        if v_isSharedCheck_3756_ == 0 {
                            v___x_3748_ = v_v_3725_;
                            v_isShared_3749_ = v_isSharedCheck_3756_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3746_);
                            lean_dec(v_v_3725_);
                            v___x_3748_ = lean_box(0);
                            v_isShared_3749_ = v_isSharedCheck_3756_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3757_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3757_, 0, v_x_3712_);
                        lean_ctor_set(v___x_3757_, 1, v_x_3713_);
                        v___y_3729_ = v___x_3757_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3730_ = lean_array_fset(v_xs_x27_3727_, v_j_3719_, v___y_3729_);
                lean_dec(v_j_3719_);
                if v_isShared_3724_ == 0 {
                    lean_ctor_set(v___x_3723_, 0, v___x_3730_);
                    v___x_3732_ = v___x_3723_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
                    v___x_3732_ = v_reuseFailAlloc_3733_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3732_;
            }
            4 => {
                v___x_3739_ = lean_name_eq(v_x_3712_, v_key_3734_);
                if v___x_3739_ == 0 {
                    lean_del_object(v___x_3737_);
                    v___x_3740_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3734_,
                        v_val_3735_,
                        v_x_3712_,
                        v_x_3713_,
                    );
                    v___x_3741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3741_, 0, v___x_3740_);
                    v___y_3729_ = v___x_3741_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3735_);
                    lean_dec(v_key_3734_);
                    if v_isShared_3738_ == 0 {
                        lean_ctor_set(v___x_3737_, 1, v_x_3713_);
                        lean_ctor_set(v___x_3737_, 0, v_x_3712_);
                        v___x_3743_ = v___x_3737_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3744_, 0, v_x_3712_);
                        lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_x_3713_);
                        v___x_3743_ = v_reuseFailAlloc_3744_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3729_ = v___x_3743_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3750_ = lean_usize_shift_right(v_x_3710_, v___x_3715_);
                v___x_3751_ = lean_usize_add(v_x_3711_, v___x_3716_);
                v___x_3752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg(v_node_3746_, v___x_3750_, v___x_3751_, v_x_3712_, v_x_3713_);
                if v_isShared_3749_ == 0 {
                    lean_ctor_set(v___x_3748_, 0, v___x_3752_);
                    v___x_3754_ = v___x_3748_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3752_);
                    v___x_3754_ = v_reuseFailAlloc_3755_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3729_ = v___x_3754_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3764_ == 0 {
                    v___x_3766_ = v___x_3763_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_ks_3760_);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_vs_3761_);
                    v___x_3766_ = v_reuseFailAlloc_3780_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3767_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v___x_3766_, v_x_3712_, v_x_3713_);
                v___x_3775_ = 7usize;
                v___x_3776_ = lean_usize_dec_le(v___x_3775_, v_x_3711_);
                if v___x_3776_ == 0 {
                    v___x_3777_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3767_);
                    v___x_3778_ = lean_unsigned_to_nat(4);
                    v___x_3779_ = lean_nat_dec_lt(v___x_3777_, v___x_3778_);
                    lean_dec(v___x_3777_);
                    v___y_3769_ = v___x_3779_;
                    state = 10;
                    continue;
                } else {
                    v___y_3769_ = v___x_3776_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3769_ == 0 {
                    v_ks_3770_ = lean_ctor_get(v_newNode_3767_, 0);
                    lean_inc_ref(v_ks_3770_);
                    v_vs_3771_ = lean_ctor_get(v_newNode_3767_, 1);
                    lean_inc_ref(v_vs_3771_);
                    lean_dec_ref(v_newNode_3767_);
                    v___x_3772_ = lean_unsigned_to_nat(0);
                    v___x_3773_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
                    v___x_3774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_x_3711_, v_ks_3770_, v_vs_3771_, v___x_3772_, v___x_3773_);
                    lean_dec_ref(v_vs_3771_);
                    lean_dec_ref(v_ks_3770_);
                    return v___x_3774_;
                } else {
                    return v_newNode_3767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(
    mut v_depth_3782_: usize,
    mut v_keys_3783_: *mut LeanObject,
    mut v_vals_3784_: *mut LeanObject,
    mut v_i_3785_: *mut LeanObject,
    mut v_entries_3786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v_k_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3792_: u64 = 0;
    let mut v_h_3793_: usize = 0;
    let mut v___x_3794_: usize = 0;
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: usize = 0;
    let mut v_h_3799_: usize = 0;
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: u64 = 0;
    let mut v_hash_3804_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3787_ = lean_array_get_size(v_keys_3783_);
                v___x_3788_ = lean_nat_dec_lt(v_i_3785_, v___x_3787_);
                if v___x_3788_ == 0 {
                    lean_dec(v_i_3785_);
                    return v_entries_3786_;
                } else {
                    v_k_3789_ = lean_array_fget_borrowed(v_keys_3783_, v_i_3785_);
                    v_v_3790_ = lean_array_fget_borrowed(v_vals_3784_, v_i_3785_);
                    if lean_obj_tag(v_k_3789_) == 0 {
                        v___x_3803_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0);
                        v___y_3792_ = v___x_3803_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3804_ = lean_ctor_get_uint64(
                            v_k_3789_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_3792_ = v_hash_3804_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3793_ = lean_uint64_to_usize(v___y_3792_);
                v___x_3794_ = 5usize;
                v___x_3795_ = lean_unsigned_to_nat(1);
                v___x_3796_ = 1usize;
                v___x_3797_ = lean_usize_sub(v_depth_3782_, v___x_3796_);
                v___x_3798_ = lean_usize_mul(v___x_3794_, v___x_3797_);
                v_h_3799_ = lean_usize_shift_right(v_h_3793_, v___x_3798_);
                v___x_3800_ = lean_nat_add(v_i_3785_, v___x_3795_);
                lean_dec(v_i_3785_);
                lean_inc(v_v_3790_);
                lean_inc(v_k_3789_);
                v___x_3801_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg(v_entries_3786_, v_h_3799_, v_depth_3782_, v_k_3789_, v_v_3790_);
                v_i_3785_ = v___x_3800_;
                v_entries_3786_ = v___x_3801_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(
    mut v_depth_3805_: *mut LeanObject,
    mut v_keys_3806_: *mut LeanObject,
    mut v_vals_3807_: *mut LeanObject,
    mut v_i_3808_: *mut LeanObject,
    mut v_entries_3809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3810_: usize = 0;
    let mut v_res_3811_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3810_ = lean_unbox_usize(v_depth_3805_);
    lean_dec(v_depth_3805_);
    v_res_3811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_boxed_3810_, v_keys_3806_, v_vals_3807_, v_i_3808_, v_entries_3809_);
    lean_dec_ref(v_vals_3807_);
    lean_dec_ref(v_keys_3806_);
    return v_res_3811_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_x_3812_: *mut LeanObject,
    mut v_x_3813_: *mut LeanObject,
    mut v_x_3814_: *mut LeanObject,
    mut v_x_3815_: *mut LeanObject,
    mut v_x_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_730__boxed_3817_: usize = 0;
    let mut v_x_731__boxed_3818_: usize = 0;
    let mut v_res_3819_: *mut LeanObject = core::ptr::null_mut();
    v_x_730__boxed_3817_ = lean_unbox_usize(v_x_3813_);
    lean_dec(v_x_3813_);
    v_x_731__boxed_3818_ = lean_unbox_usize(v_x_3814_);
    lean_dec(v_x_3814_);
    v_res_3819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_3812_, v_x_730__boxed_3817_, v_x_731__boxed_3818_, v_x_3815_, v_x_3816_);
    return v_res_3819_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_3820_: *mut LeanObject,
    mut v_x_3821_: *mut LeanObject,
    mut v_x_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3824_: u64 = 0;
    let mut v___x_3825_: usize = 0;
    let mut v___x_3826_: usize = 0;
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: u64 = 0;
    let mut v_hash_3829_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3821_) == 0 {
                    v___x_3828_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0);
                    v___y_3824_ = v___x_3828_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3829_ = lean_ctor_get_uint64(
                        v_x_3821_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_3824_ = v_hash_3829_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3825_ = lean_uint64_to_usize(v___y_3824_);
                v___x_3826_ = 1usize;
                v___x_3827_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_3820_, v___x_3825_, v___x_3826_, v_x_3821_, v_x_3822_);
                return v___x_3827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    v___x_3833_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__2;
    v___x_3834_ = lean_unsigned_to_nat(14);
    v___x_3835_ = lean_unsigned_to_nat(177);
    v___x_3836_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__1;
    v___x_3837_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__0;
    v___x_3838_ = l_mkPanicMessageWithDecl(
        v___x_3837_,
        v___x_3836_,
        v___x_3835_,
        v___x_3834_,
        v___x_3833_,
    );
    return v___x_3838_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3(
    mut v_newState_3839_: *mut LeanObject,
    mut v_x_3840_: *mut LeanObject,
    mut v_x_3841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v___y_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constNames_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revNames_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut v_constNames_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3841_) == 0 {
                    return v_x_3840_;
                } else {
                    v_head_3842_ = lean_ctor_get(v_x_3841_, 0);
                    v_tail_3843_ = lean_ctor_get(v_x_3841_, 1);
                    v_isSharedCheck_3868_ = (!lean_is_exclusive(v_x_3841_)) as u8;
                    if v_isSharedCheck_3868_ == 0 {
                        v___x_3845_ = v_x_3841_;
                        v_isShared_3846_ = v_isSharedCheck_3868_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3843_);
                        lean_inc(v_head_3842_);
                        lean_dec(v_x_3841_);
                        v___x_3845_ = lean_box(0);
                        v_isShared_3846_ = v_isSharedCheck_3868_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_constNames_3863_ = lean_ctor_get(v_newState_3839_, 0);
                v___x_3864_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg(v_constNames_3863_, v_head_3842_);
                if lean_obj_tag(v___x_3864_) == 0 {
                    v___x_3865_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__3_once), _init_l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___closed__3);
                    v___x_3866_ = l_panic___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__2(v___x_3865_);
                    v___y_3848_ = v___x_3866_;
                    state = 2;
                    continue;
                } else {
                    v_val_3867_ = lean_ctor_get(v___x_3864_, 0);
                    lean_inc(v_val_3867_);
                    lean_dec_ref_known(v___x_3864_, 1);
                    v___y_3848_ = v_val_3867_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_constNames_3849_ = lean_ctor_get(v_x_3840_, 0);
                v_revNames_3850_ = lean_ctor_get(v_x_3840_, 1);
                v_isSharedCheck_3862_ = (!lean_is_exclusive(v_x_3840_)) as u8;
                if v_isSharedCheck_3862_ == 0 {
                    v___x_3852_ = v_x_3840_;
                    v_isShared_3853_ = v_isSharedCheck_3862_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_revNames_3850_);
                    lean_inc(v_constNames_3849_);
                    lean_dec(v_x_3840_);
                    v___x_3852_ = lean_box(0);
                    v_isShared_3853_ = v_isSharedCheck_3862_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_head_3842_);
                v___x_3854_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0___redArg(v_constNames_3849_, v_head_3842_, v___y_3848_);
                if v_isShared_3846_ == 0 {
                    lean_ctor_set(v___x_3845_, 1, v_revNames_3850_);
                    v___x_3856_ = v___x_3845_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_head_3842_);
                    lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_revNames_3850_);
                    v___x_3856_ = v_reuseFailAlloc_3861_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3853_ == 0 {
                    lean_ctor_set(v___x_3852_, 1, v___x_3856_);
                    lean_ctor_set(v___x_3852_, 0, v___x_3854_);
                    v___x_3858_ = v___x_3852_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3854_);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 1, v___x_3856_);
                    v___x_3858_ = v_reuseFailAlloc_3860_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_3840_ = v___x_3858_;
                v_x_3841_ = v_tail_3843_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3___boxed(
    mut v_newState_3869_: *mut LeanObject,
    mut v_x_3870_: *mut LeanObject,
    mut v_x_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3872_: *mut LeanObject = core::ptr::null_mut();
    v_res_3872_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3(v_newState_3869_, v_x_3870_, v_x_3871_);
    lean_dec_ref(v_newState_3869_);
    return v_res_3872_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_(
    mut v_oldState_3875_: *mut LeanObject,
    mut v_newState_3876_: *mut LeanObject,
    mut v_x_3877_: *mut LeanObject,
    mut v_s_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_revNames_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revNames_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNames_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    v_revNames_3879_ = lean_ctor_get(v_newState_3876_, 1);
    v_revNames_3880_ = lean_ctor_get(v_oldState_3875_, 1);
    v___x_3881_ = l_List_lengthTR___redArg(v_revNames_3879_);
    v___x_3882_ = l_List_lengthTR___redArg(v_revNames_3880_);
    v___x_3883_ = lean_nat_sub(v___x_3881_, v___x_3882_);
    lean_dec(v___x_3882_);
    lean_dec(v___x_3881_);
    v___x_3884_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0___closed__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_;
    lean_inc(v_revNames_3879_);
    v_newNames_3885_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        lean_box(0),
        v_revNames_3879_,
        v_revNames_3879_,
        v___x_3883_,
        v___x_3884_,
    );
    v___x_3886_ = l_List_foldl___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__3(v_newState_3876_, v_s_3878_, v_newNames_3885_);
    lean_dec_ref(v_newState_3876_);
    return v___x_3886_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2____boxed(
    mut v_oldState_3887_: *mut LeanObject,
    mut v_newState_3888_: *mut LeanObject,
    mut v_x_3889_: *mut LeanObject,
    mut v_s_3890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3891_: *mut LeanObject = core::ptr::null_mut();
    v_res_3891_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_(v_oldState_3887_, v_newState_3888_, v_x_3889_, v_s_3890_);
    lean_dec(v_x_3889_);
    lean_dec_ref(v_oldState_3887_);
    return v_res_3891_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_(
    mut v___x_3892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    v___x_3894_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3894_, 0, v___x_3892_);
    return v___x_3894_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2____boxed(
    mut v___x_3895_: *mut LeanObject,
    mut v___y_3896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3897_: *mut LeanObject = core::ptr::null_mut();
    v_res_3897_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_(v___x_3895_);
    return v_res_3897_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3900_: *mut LeanObject = core::ptr::null_mut();
    v___x_3899_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default___closed__2,
    );
    v___f_3900_ = lean_alloc_closure(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_3900_, 0, v___x_3899_);
    return v___f_3900_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    v___f_3904_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_);
    v___x_3905_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_;
    v___x_3906_ = lean_box(0);
    v___x_3907_ = l_Lean_registerEnvExtension___redArg(v___f_3904_, v___x_3905_, v___x_3906_);
    return v___x_3907_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2____boxed(
    mut v_a_3908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3909_: *mut LeanObject = core::ptr::null_mut();
    v_res_3909_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_();
    return v_res_3909_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_3910_: *mut LeanObject,
    mut v_x_3911_: *mut LeanObject,
    mut v_x_3912_: *mut LeanObject,
    mut v_x_3913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0___redArg(v_x_3911_, v_x_3912_, v_x_3913_);
    return v___x_3914_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_3915_: *mut LeanObject,
    mut v_x_3916_: *mut LeanObject,
    mut v_x_3917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    v___x_3918_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg(v_x_3916_, v_x_3917_);
    return v___x_3918_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b2_3919_: *mut LeanObject,
    mut v_x_3920_: *mut LeanObject,
    mut v_x_3921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3922_: *mut LeanObject = core::ptr::null_mut();
    v_res_3922_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1(v_00_u03b2_3919_, v_x_3920_, v_x_3921_);
    lean_dec(v_x_3921_);
    lean_dec_ref(v_x_3920_);
    return v_res_3922_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_3923_: *mut LeanObject,
    mut v_x_3924_: *mut LeanObject,
    mut v_x_3925_: usize,
    mut v_x_3926_: usize,
    mut v_x_3927_: *mut LeanObject,
    mut v_x_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    v___x_3929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_3924_, v_x_3925_, v_x_3926_, v_x_3927_, v_x_3928_);
    return v___x_3929_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_3930_: *mut LeanObject,
    mut v_x_3931_: *mut LeanObject,
    mut v_x_3932_: *mut LeanObject,
    mut v_x_3933_: *mut LeanObject,
    mut v_x_3934_: *mut LeanObject,
    mut v_x_3935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1065__boxed_3936_: usize = 0;
    let mut v_x_1066__boxed_3937_: usize = 0;
    let mut v_res_3938_: *mut LeanObject = core::ptr::null_mut();
    v_x_1065__boxed_3936_ = lean_unbox_usize(v_x_3932_);
    lean_dec(v_x_3932_);
    v_x_1066__boxed_3937_ = lean_unbox_usize(v_x_3933_);
    lean_dec(v_x_3933_);
    v_res_3938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_3930_, v_x_3931_, v_x_1065__boxed_3936_, v_x_1066__boxed_3937_, v_x_3934_, v_x_3935_);
    return v_res_3938_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b2_3939_: *mut LeanObject,
    mut v_x_3940_: *mut LeanObject,
    mut v_x_3941_: usize,
    mut v_x_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_3940_, v_x_3941_, v_x_3942_);
    return v___x_3943_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_00_u03b2_3944_: *mut LeanObject,
    mut v_x_3945_: *mut LeanObject,
    mut v_x_3946_: *mut LeanObject,
    mut v_x_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1082__boxed_3948_: usize = 0;
    let mut v_res_3949_: *mut LeanObject = core::ptr::null_mut();
    v_x_1082__boxed_3948_ = lean_unbox_usize(v_x_3946_);
    lean_dec(v_x_3946_);
    v_res_3949_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_3944_, v_x_3945_, v_x_1082__boxed_3948_, v_x_3947_);
    lean_dec(v_x_3947_);
    lean_dec_ref(v_x_3945_);
    return v_res_3949_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2(
    mut v_00_u03b2_3950_: *mut LeanObject,
    mut v_n_3951_: *mut LeanObject,
    mut v_k_3952_: *mut LeanObject,
    mut v_v_3953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    v___x_3954_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_n_3951_, v_k_3952_, v_v_3953_);
    return v___x_3954_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3(
    mut v_00_u03b2_3955_: *mut LeanObject,
    mut v_depth_3956_: usize,
    mut v_keys_3957_: *mut LeanObject,
    mut v_vals_3958_: *mut LeanObject,
    mut v_heq_3959_: *mut LeanObject,
    mut v_i_3960_: *mut LeanObject,
    mut v_entries_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    v___x_3962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_3956_, v_keys_3957_, v_vals_3958_, v_i_3960_, v_entries_3961_);
    return v___x_3962_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_3963_: *mut LeanObject,
    mut v_depth_3964_: *mut LeanObject,
    mut v_keys_3965_: *mut LeanObject,
    mut v_vals_3966_: *mut LeanObject,
    mut v_heq_3967_: *mut LeanObject,
    mut v_i_3968_: *mut LeanObject,
    mut v_entries_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3970_: usize = 0;
    let mut v_res_3971_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3970_ = lean_unbox_usize(v_depth_3964_);
    lean_dec(v_depth_3964_);
    v_res_3971_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_00_u03b2_3963_, v_depth_boxed_3970_, v_keys_3965_, v_vals_3966_, v_heq_3967_, v_i_3968_, v_entries_3969_);
    lean_dec_ref(v_vals_3966_);
    lean_dec_ref(v_keys_3965_);
    return v_res_3971_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6(
    mut v_00_u03b2_3972_: *mut LeanObject,
    mut v_keys_3973_: *mut LeanObject,
    mut v_vals_3974_: *mut LeanObject,
    mut v_heq_3975_: *mut LeanObject,
    mut v_i_3976_: *mut LeanObject,
    mut v_k_3977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    v___x_3978_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_3973_, v_vals_3974_, v_i_3976_, v_k_3977_);
    return v___x_3978_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(
    mut v_00_u03b2_3979_: *mut LeanObject,
    mut v_keys_3980_: *mut LeanObject,
    mut v_vals_3981_: *mut LeanObject,
    mut v_heq_3982_: *mut LeanObject,
    mut v_i_3983_: *mut LeanObject,
    mut v_k_3984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3985_: *mut LeanObject = core::ptr::null_mut();
    v_res_3985_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2_spec__6(v_00_u03b2_3979_, v_keys_3980_, v_vals_3981_, v_heq_3982_, v_i_3983_, v_k_3984_);
    lean_dec(v_k_3984_);
    lean_dec_ref(v_vals_3981_);
    lean_dec_ref(v_keys_3980_);
    return v_res_3985_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_3986_: *mut LeanObject,
    mut v_x_3987_: *mut LeanObject,
    mut v_x_3988_: *mut LeanObject,
    mut v_x_3989_: *mut LeanObject,
    mut v_x_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    v___x_3991_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_x_3987_, v_x_3988_, v_x_3989_, v_x_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addSimpleGroundDecl___lam__0(
    mut v_declName_3992_: *mut LeanObject,
    mut v_expr_3993_: *mut LeanObject,
    mut v_s_3994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_constNames_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_revNames_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_constNames_3995_ = lean_ctor_get(v_s_3994_, 0);
                v_revNames_3996_ = lean_ctor_get(v_s_3994_, 1);
                v_isSharedCheck_4005_ = (!lean_is_exclusive(v_s_3994_)) as u8;
                if v_isSharedCheck_4005_ == 0 {
                    v___x_3998_ = v_s_3994_;
                    v_isShared_3999_ = v_isSharedCheck_4005_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_revNames_3996_);
                    lean_inc(v_constNames_3995_);
                    lean_dec(v_s_3994_);
                    v___x_3998_ = lean_box(0);
                    v_isShared_3999_ = v_isSharedCheck_4005_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_declName_3992_);
                v___x_4000_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__0___redArg(v_constNames_3995_, v_declName_3992_, v_expr_3993_);
                v___x_4001_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_4001_, 0, v_declName_3992_);
                lean_ctor_set(v___x_4001_, 1, v_revNames_3996_);
                if v_isShared_3999_ == 0 {
                    lean_ctor_set(v___x_3998_, 1, v___x_4001_);
                    lean_ctor_set(v___x_3998_, 0, v___x_4000_);
                    v___x_4003_ = v___x_3998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4000_);
                    lean_ctor_set(v_reuseFailAlloc_4004_, 1, v___x_4001_);
                    v___x_4003_ = v_reuseFailAlloc_4004_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_addSimpleGroundDecl(
    mut v_env_4006_: *mut LeanObject,
    mut v_declName_4007_: *mut LeanObject,
    mut v_expr_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    v___x_4009_ =
        l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_simpleGroundDeclExt;
    v_asyncMode_4010_ = lean_ctor_get(v___x_4009_, 2);
    v___f_4011_ = lean_alloc_closure(
        l_Lean_Compiler_LCNF_addSimpleGroundDecl___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4011_, 0, v_declName_4007_);
    lean_closure_set(v___f_4011_, 1, v_expr_4008_);
    v___x_4012_ = lean_box(0);
    v___x_4013_ = l_Lean_EnvExtension_modifyState___redArg(
        v___x_4009_,
        v_env_4006_,
        v___f_4011_,
        v_asyncMode_4010_,
        v___x_4012_,
    );
    return v___x_4013_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSimpleGroundExpr(
    mut v_env_4014_: *mut LeanObject,
    mut v_declName_4015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constNames_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    v___x_4016_ =
        l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_simpleGroundDeclExt;
    v_asyncMode_4017_ = lean_ctor_get(v___x_4016_, 2);
    v___x_4018_ = l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default;
    v___x_4019_ = lean_box(0);
    v___x_4020_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4018_,
        v___x_4016_,
        v_env_4014_,
        v_asyncMode_4017_,
        v___x_4019_,
    );
    v_constNames_4021_ = lean_ctor_get(v___x_4020_, 0);
    lean_inc_ref(v_constNames_4021_);
    lean_dec(v___x_4020_);
    v___x_4022_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg(v_constNames_4021_, v_declName_4015_);
    lean_dec_ref(v_constNames_4021_);
    return v___x_4022_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getSimpleGroundExpr___boxed(
    mut v_env_4023_: *mut LeanObject,
    mut v_declName_4024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4025_: *mut LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Lean_Compiler_LCNF_getSimpleGroundExpr(v_env_4023_, v_declName_4024_);
    lean_dec(v_declName_4024_);
    return v_res_4025_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs_spec__0___redArg___lam__0(
    mut v_snd_4026_: *mut LeanObject,
    mut v_other_4027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    v___x_4028_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4028_, 0, v_other_4027_);
    v___x_4029_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4029_, 0, v___x_4028_);
    lean_ctor_set(v___x_4029_, 1, v_snd_4026_);
    v___x_4030_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4030_, 0, v___x_4029_);
    return v___x_4030_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs_spec__0___redArg(
    mut v_env_4031_: *mut LeanObject,
    mut v_a_4032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_unused_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4038_ = lean_ctor_get(v_a_4032_, 1);
                v_isSharedCheck_4052_ = (!lean_is_exclusive(v_a_4032_)) as u8;
                if v_isSharedCheck_4052_ == 0 {
                    v_unused_4053_ = lean_ctor_get(v_a_4032_, 0);
                    lean_dec(v_unused_4053_);
                    v___x_4040_ = v_a_4032_;
                    v_isShared_4041_ = v_isSharedCheck_4052_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4038_);
                    lean_dec(v_a_4032_);
                    v___x_4040_ = lean_box(0);
                    v_isShared_4041_ = v_isSharedCheck_4052_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_4034_) == 0 {
                    lean_dec_ref(v_env_4031_);
                    v_a_4035_ = lean_ctor_get(v___y_4034_, 0);
                    lean_inc(v_a_4035_);
                    lean_dec_ref_known(v___y_4034_, 1);
                    return v_a_4035_;
                } else {
                    v_a_4036_ = lean_ctor_get(v___y_4034_, 0);
                    lean_inc(v_a_4036_);
                    lean_dec_ref_known(v___y_4034_, 1);
                    v_a_4032_ = v_a_4036_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_env_4031_);
                v___x_4042_ = l_Lean_Compiler_LCNF_getSimpleGroundExpr(v_env_4031_, v_snd_4038_);
                if lean_obj_tag(v___x_4042_) == 1 {
                    v_val_4043_ = lean_ctor_get(v___x_4042_, 0);
                    lean_inc(v_val_4043_);
                    if lean_obj_tag(v_val_4043_) == 4 {
                        lean_dec_ref_known(v___x_4042_, 1);
                        lean_dec(v_snd_4038_);
                        v_n_4044_ = lean_ctor_get(v_val_4043_, 0);
                        lean_inc(v_n_4044_);
                        lean_dec_ref_known(v_val_4043_, 1);
                        v___x_4045_ = lean_box(0);
                        if v_isShared_4041_ == 0 {
                            lean_ctor_set(v___x_4040_, 1, v_n_4044_);
                            lean_ctor_set(v___x_4040_, 0, v___x_4045_);
                            v___x_4047_ = v___x_4040_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4045_);
                            lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_n_4044_);
                            v___x_4047_ = v_reuseFailAlloc_4049_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_4043_);
                        lean_del_object(v___x_4040_);
                        v___x_4050_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs_spec__0___redArg___lam__0(v_snd_4038_, v___x_4042_);
                        v___y_4034_ = v___x_4050_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4040_);
                    v___x_4051_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs_spec__0___redArg___lam__0(v_snd_4038_, v___x_4042_);
                    v___y_4034_ = v___x_4051_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_4032_ = v___x_4047_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs(
    mut v_env_4054_: *mut LeanObject,
    mut v_declName_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4059_: *mut LeanObject = core::ptr::null_mut();
    v___x_4056_ = lean_box(0);
    v___x_4057_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4057_, 0, v___x_4056_);
    lean_ctor_set(v___x_4057_, 1, v_declName_4055_);
    v___x_4058_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs_spec__0___redArg(v_env_4054_, v___x_4057_);
    v_fst_4059_ = lean_ctor_get(v___x_4058_, 0);
    lean_inc(v_fst_4059_);
    lean_dec_ref(v___x_4058_);
    if lean_obj_tag(v_fst_4059_) == 0 {
        return v___x_4056_;
    } else {
        let mut v_val_4060_: *mut LeanObject = core::ptr::null_mut();
        v_val_4060_ = lean_ctor_get(v_fst_4059_, 0);
        lean_inc(v_val_4060_);
        lean_dec_ref_known(v_fst_4059_, 1);
        return v_val_4060_;
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs_spec__0(
    mut v_env_4061_: *mut LeanObject,
    mut v_inst_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    v___x_4064_ = l___private_Init_While_0__whileM_erased___at___00Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs_spec__0___redArg(v_env_4061_, v_a_4063_);
    return v___x_4064_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4065_: *mut LeanObject,
    mut v_i_4066_: *mut LeanObject,
    mut v_k_4067_: *mut LeanObject,
) -> u8 {
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    let mut v_k_x27_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4068_ = lean_array_get_size(v_keys_4065_);
                v___x_4069_ = lean_nat_dec_lt(v_i_4066_, v___x_4068_);
                if v___x_4069_ == 0 {
                    lean_dec(v_i_4066_);
                    return v___x_4069_;
                } else {
                    v_k_x27_4070_ = lean_array_fget_borrowed(v_keys_4065_, v_i_4066_);
                    v___x_4071_ = lean_name_eq(v_k_4067_, v_k_x27_4070_);
                    if v___x_4071_ == 0 {
                        v___x_4072_ = lean_unsigned_to_nat(1);
                        v___x_4073_ = lean_nat_add(v_i_4066_, v___x_4072_);
                        lean_dec(v_i_4066_);
                        v_i_4066_ = v___x_4073_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4066_);
                        return v___x_4071_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4075_: *mut LeanObject,
    mut v_i_4076_: *mut LeanObject,
    mut v_k_4077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4078_: u8 = 0;
    let mut v_r_4079_: *mut LeanObject = core::ptr::null_mut();
    v_res_4078_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1___redArg(v_keys_4075_, v_i_4076_, v_k_4077_);
    lean_dec(v_k_4077_);
    lean_dec_ref(v_keys_4075_);
    v_r_4079_ = lean_box((v_res_4078_) as usize);
    return v_r_4079_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0___redArg(
    mut v_x_4080_: *mut LeanObject,
    mut v_x_4081_: usize,
    mut v_x_4082_: *mut LeanObject,
) -> u8 {
    let mut v_es_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: usize = 0;
    let mut v___x_4086_: usize = 0;
    let mut v___x_4087_: usize = 0;
    let mut v_j_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: u8 = 0;
    let mut v_node_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: usize = 0;
    let mut v___x_4095_: u8 = 0;
    let mut v_ks_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4080_) == 0 {
                    v_es_4083_ = lean_ctor_get(v_x_4080_, 0);
                    v___x_4084_ = lean_box(2);
                    v___x_4085_ = 5usize;
                    v___x_4086_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__1);
                    v___x_4087_ = lean_usize_land(v_x_4081_, v___x_4086_);
                    v_j_4088_ = lean_usize_to_nat(v___x_4087_);
                    v___x_4089_ = lean_array_get_borrowed(v___x_4084_, v_es_4083_, v_j_4088_);
                    lean_dec(v_j_4088_);
                    match lean_obj_tag(v___x_4089_) {
                        0 => {
                            v_key_4090_ = lean_ctor_get(v___x_4089_, 0);
                            v___x_4091_ = lean_name_eq(v_x_4082_, v_key_4090_);
                            return v___x_4091_;
                        }
                        1 => {
                            v_node_4092_ = lean_ctor_get(v___x_4089_, 0);
                            v___x_4093_ = lean_usize_shift_right(v_x_4081_, v___x_4085_);
                            v_x_4080_ = v_node_4092_;
                            v_x_4081_ = v___x_4093_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4095_ = 0;
                            return v___x_4095_;
                        }
                    }
                } else {
                    v_ks_4096_ = lean_ctor_get(v_x_4080_, 0);
                    v___x_4097_ = lean_unsigned_to_nat(0);
                    v___x_4098_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1___redArg(v_ks_4096_, v___x_4097_, v_x_4082_);
                    return v___x_4098_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0___redArg___boxed(
    mut v_x_4099_: *mut LeanObject,
    mut v_x_4100_: *mut LeanObject,
    mut v_x_4101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_140__boxed_4102_: usize = 0;
    let mut v_res_4103_: u8 = 0;
    let mut v_r_4104_: *mut LeanObject = core::ptr::null_mut();
    v_x_140__boxed_4102_ = lean_unbox_usize(v_x_4100_);
    lean_dec(v_x_4100_);
    v_res_4103_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0___redArg(v_x_4099_, v_x_140__boxed_4102_, v_x_4101_);
    lean_dec(v_x_4101_);
    lean_dec_ref(v_x_4099_);
    v_r_4104_ = lean_box((v_res_4103_) as usize);
    return v_r_4104_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0___redArg(
    mut v_x_4105_: *mut LeanObject,
    mut v_x_4106_: *mut LeanObject,
) -> u8 {
    let mut v___y_4108_: u64 = 0;
    let mut v___x_4109_: usize = 0;
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: u64 = 0;
    let mut v_hash_4112_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4106_) == 0 {
                    v___x_4111_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0);
                    v___y_4108_ = v___x_4111_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4112_ = lean_ctor_get_uint64(
                        v_x_4106_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_4108_ = v_hash_4112_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4109_ = lean_uint64_to_usize(v___y_4108_);
                v___x_4110_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0___redArg(v_x_4105_, v___x_4109_, v_x_4106_);
                return v___x_4110_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0___redArg___boxed(
    mut v_x_4113_: *mut LeanObject,
    mut v_x_4114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4115_: u8 = 0;
    let mut v_r_4116_: *mut LeanObject = core::ptr::null_mut();
    v_res_4115_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0___redArg(v_x_4113_, v_x_4114_);
    lean_dec(v_x_4114_);
    lean_dec_ref(v_x_4113_);
    v_r_4116_ = lean_box((v_res_4115_) as usize);
    return v_r_4116_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isSimpleGroundDecl(
    mut v_env_4117_: *mut LeanObject,
    mut v_declName_4118_: *mut LeanObject,
) -> u8 {
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constNames_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    v___x_4119_ =
        l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_simpleGroundDeclExt;
    v_asyncMode_4120_ = lean_ctor_get(v___x_4119_, 2);
    v___x_4121_ = l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default;
    v___x_4122_ = lean_box(0);
    v___x_4123_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4121_,
        v___x_4119_,
        v_env_4117_,
        v_asyncMode_4120_,
        v___x_4122_,
    );
    v_constNames_4124_ = lean_ctor_get(v___x_4123_, 0);
    lean_inc_ref(v_constNames_4124_);
    lean_dec(v___x_4123_);
    v___x_4125_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0___redArg(v_constNames_4124_, v_declName_4118_);
    lean_dec_ref(v_constNames_4124_);
    return v___x_4125_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isSimpleGroundDecl___boxed(
    mut v_env_4126_: *mut LeanObject,
    mut v_declName_4127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4128_: u8 = 0;
    let mut v_r_4129_: *mut LeanObject = core::ptr::null_mut();
    v_res_4128_ = l_Lean_Compiler_LCNF_isSimpleGroundDecl(v_env_4126_, v_declName_4127_);
    lean_dec(v_declName_4127_);
    v_r_4129_ = lean_box((v_res_4128_) as usize);
    return v_r_4129_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0(
    mut v_00_u03b2_4130_: *mut LeanObject,
    mut v_x_4131_: *mut LeanObject,
    mut v_x_4132_: *mut LeanObject,
) -> u8 {
    let mut v___x_4133_: u8 = 0;
    v___x_4133_ = l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0___redArg(v_x_4131_, v_x_4132_);
    return v___x_4133_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0___boxed(
    mut v_00_u03b2_4134_: *mut LeanObject,
    mut v_x_4135_: *mut LeanObject,
    mut v_x_4136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4137_: u8 = 0;
    let mut v_r_4138_: *mut LeanObject = core::ptr::null_mut();
    v_res_4137_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0(
            v_00_u03b2_4134_,
            v_x_4135_,
            v_x_4136_,
        );
    lean_dec(v_x_4136_);
    lean_dec_ref(v_x_4135_);
    v_r_4138_ = lean_box((v_res_4137_) as usize);
    return v_r_4138_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0(
    mut v_00_u03b2_4139_: *mut LeanObject,
    mut v_x_4140_: *mut LeanObject,
    mut v_x_4141_: usize,
    mut v_x_4142_: *mut LeanObject,
) -> u8 {
    let mut v___x_4143_: u8 = 0;
    v___x_4143_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0___redArg(v_x_4140_, v_x_4141_, v_x_4142_);
    return v___x_4143_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0___boxed(
    mut v_00_u03b2_4144_: *mut LeanObject,
    mut v_x_4145_: *mut LeanObject,
    mut v_x_4146_: *mut LeanObject,
    mut v_x_4147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_220__boxed_4148_: usize = 0;
    let mut v_res_4149_: u8 = 0;
    let mut v_r_4150_: *mut LeanObject = core::ptr::null_mut();
    v_x_220__boxed_4148_ = lean_unbox_usize(v_x_4146_);
    lean_dec(v_x_4146_);
    v_res_4149_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0(v_00_u03b2_4144_, v_x_4145_, v_x_220__boxed_4148_, v_x_4147_);
    lean_dec(v_x_4147_);
    lean_dec_ref(v_x_4145_);
    v_r_4150_ = lean_box((v_res_4149_) as usize);
    return v_r_4150_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4151_: *mut LeanObject,
    mut v_keys_4152_: *mut LeanObject,
    mut v_vals_4153_: *mut LeanObject,
    mut v_heq_4154_: *mut LeanObject,
    mut v_i_4155_: *mut LeanObject,
    mut v_k_4156_: *mut LeanObject,
) -> u8 {
    let mut v___x_4157_: u8 = 0;
    v___x_4157_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1___redArg(v_keys_4152_, v_i_4155_, v_k_4156_);
    return v___x_4157_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4158_: *mut LeanObject,
    mut v_keys_4159_: *mut LeanObject,
    mut v_vals_4160_: *mut LeanObject,
    mut v_heq_4161_: *mut LeanObject,
    mut v_i_4162_: *mut LeanObject,
    mut v_k_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4164_: u8 = 0;
    let mut v_r_4165_: *mut LeanObject = core::ptr::null_mut();
    v_res_4164_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Compiler_LCNF_isSimpleGroundDecl_spec__0_spec__0_spec__1(v_00_u03b2_4158_, v_keys_4159_, v_vals_4160_, v_heq_4161_, v_i_4162_, v_k_4163_);
    lean_dec(v_k_4163_);
    lean_dec_ref(v_vals_4160_);
    lean_dec_ref(v_keys_4159_);
    v_r_4165_ = lean_box((v_res_4164_) as usize);
    return v_r_4165_;
}
pub unsafe fn l_Lean_Compiler_LCNF_uint64ToByteArrayLE(mut v_n_4166_: u64) -> *mut LeanObject {
    let mut v___x_4167_: u8 = 0;
    let mut v___x_4168_: u64 = 0;
    let mut v___x_4169_: u64 = 0;
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: u64 = 0;
    let mut v___x_4172_: u64 = 0;
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: u64 = 0;
    let mut v___x_4175_: u64 = 0;
    let mut v___x_4176_: u8 = 0;
    let mut v___x_4177_: u64 = 0;
    let mut v___x_4178_: u64 = 0;
    let mut v___x_4179_: u8 = 0;
    let mut v___x_4180_: u64 = 0;
    let mut v___x_4181_: u64 = 0;
    let mut v___x_4182_: u8 = 0;
    let mut v___x_4183_: u64 = 0;
    let mut v___x_4184_: u64 = 0;
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: u64 = 0;
    let mut v___x_4187_: u64 = 0;
    let mut v___x_4188_: u8 = 0;
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    v___x_4167_ = lean_uint64_to_uint8(v_n_4166_);
    v___x_4168_ = 8u64;
    v___x_4169_ = lean_uint64_shift_right(v_n_4166_, v___x_4168_);
    v___x_4170_ = lean_uint64_to_uint8(v___x_4169_);
    v___x_4171_ = 16u64;
    v___x_4172_ = lean_uint64_shift_right(v_n_4166_, v___x_4171_);
    v___x_4173_ = lean_uint64_to_uint8(v___x_4172_);
    v___x_4174_ = 24u64;
    v___x_4175_ = lean_uint64_shift_right(v_n_4166_, v___x_4174_);
    v___x_4176_ = lean_uint64_to_uint8(v___x_4175_);
    v___x_4177_ = 32u64;
    v___x_4178_ = lean_uint64_shift_right(v_n_4166_, v___x_4177_);
    v___x_4179_ = lean_uint64_to_uint8(v___x_4178_);
    v___x_4180_ = 40u64;
    v___x_4181_ = lean_uint64_shift_right(v_n_4166_, v___x_4180_);
    v___x_4182_ = lean_uint64_to_uint8(v___x_4181_);
    v___x_4183_ = 48u64;
    v___x_4184_ = lean_uint64_shift_right(v_n_4166_, v___x_4183_);
    v___x_4185_ = lean_uint64_to_uint8(v___x_4184_);
    v___x_4186_ = 56u64;
    v___x_4187_ = lean_uint64_shift_right(v_n_4166_, v___x_4186_);
    v___x_4188_ = lean_uint64_to_uint8(v___x_4187_);
    v___x_4189_ = lean_unsigned_to_nat(8);
    v___x_4190_ = lean_mk_empty_array_with_capacity(v___x_4189_);
    v___x_4191_ = lean_box((v___x_4167_) as usize);
    v___x_4192_ = lean_array_push(v___x_4190_, v___x_4191_);
    v___x_4193_ = lean_box((v___x_4170_) as usize);
    v___x_4194_ = lean_array_push(v___x_4192_, v___x_4193_);
    v___x_4195_ = lean_box((v___x_4173_) as usize);
    v___x_4196_ = lean_array_push(v___x_4194_, v___x_4195_);
    v___x_4197_ = lean_box((v___x_4176_) as usize);
    v___x_4198_ = lean_array_push(v___x_4196_, v___x_4197_);
    v___x_4199_ = lean_box((v___x_4179_) as usize);
    v___x_4200_ = lean_array_push(v___x_4198_, v___x_4199_);
    v___x_4201_ = lean_box((v___x_4182_) as usize);
    v___x_4202_ = lean_array_push(v___x_4200_, v___x_4201_);
    v___x_4203_ = lean_box((v___x_4185_) as usize);
    v___x_4204_ = lean_array_push(v___x_4202_, v___x_4203_);
    v___x_4205_ = lean_box((v___x_4188_) as usize);
    v___x_4206_ = lean_array_push(v___x_4204_, v___x_4205_);
    return v___x_4206_;
}
pub unsafe fn l_Lean_Compiler_LCNF_uint64ToByteArrayLE___boxed(
    mut v_n_4207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_4208_: u64 = 0;
    let mut v_res_4209_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_4208_ = lean_unbox_uint64(v_n_4207_);
    lean_dec_ref(v_n_4207_);
    v_res_4209_ = l_Lean_Compiler_LCNF_uint64ToByteArrayLE(v_n_boxed_4208_);
    return v_res_4209_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorIdx(
    mut v_x_4210_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_4210_) {
        0 => {
            let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
            v___x_4211_ = lean_unsigned_to_nat(0);
            return v___x_4211_;
        }
        1 => {
            let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
            v___x_4212_ = lean_unsigned_to_nat(1);
            return v___x_4212_;
        }
        2 => {
            let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
            v___x_4213_ = lean_unsigned_to_nat(2);
            return v___x_4213_;
        }
        3 => {
            let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
            v___x_4214_ = lean_unsigned_to_nat(3);
            return v___x_4214_;
        }
        4 => {
            let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
            v___x_4215_ = lean_unsigned_to_nat(4);
            return v___x_4215_;
        }
        5 => {
            let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
            v___x_4216_ = lean_unsigned_to_nat(5);
            return v___x_4216_;
        }
        _ => {
            let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
            v___x_4217_ = lean_unsigned_to_nat(6);
            return v___x_4217_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorIdx___boxed(
    mut v_x_4218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4219_: *mut LeanObject = core::ptr::null_mut();
    v_res_4219_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorIdx(v_x_4218_);
    lean_dec_ref(v_x_4218_);
    return v_res_4219_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(
    mut v_t_4220_: *mut LeanObject,
    mut v_k_4221_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4220_) {
        0 => {
            let mut v_arg_4222_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
            v_arg_4222_ = lean_ctor_get(v_t_4220_, 0);
            lean_inc_ref(v_arg_4222_);
            lean_dec_ref_known(v_t_4220_, 1);
            v___x_4223_ = lean_apply_1(v_k_4221_, v_arg_4222_);
            return v___x_4223_;
        }
        1 => {
            let mut v_val_4224_: u8 = 0;
            let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
            v_val_4224_ = lean_ctor_get_uint8(v_t_4220_, 0 as u32);
            lean_dec_ref_known(v_t_4220_, 0);
            v___x_4225_ = lean_box((v_val_4224_) as usize);
            v___x_4226_ = lean_apply_1(v_k_4221_, v___x_4225_);
            return v___x_4226_;
        }
        2 => {
            let mut v_val_4227_: u16 = 0;
            let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
            v_val_4227_ = lean_ctor_get_uint16(v_t_4220_, 0 as u32);
            lean_dec_ref_known(v_t_4220_, 0);
            v___x_4228_ = lean_box((v_val_4227_) as usize);
            v___x_4229_ = lean_apply_1(v_k_4221_, v___x_4228_);
            return v___x_4229_;
        }
        3 => {
            let mut v_val_4230_: u32 = 0;
            let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
            v_val_4230_ = lean_ctor_get_uint32(v_t_4220_, 0 as u32);
            lean_dec_ref_known(v_t_4220_, 0);
            v___x_4231_ = lean_box_uint32(v_val_4230_);
            v___x_4232_ = lean_apply_1(v_k_4221_, v___x_4231_);
            return v___x_4232_;
        }
        6 => {
            let mut v_elems_4233_: *mut LeanObject = core::ptr::null_mut();
            let mut v_remainingCapacity_4234_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
            v_elems_4233_ = lean_ctor_get(v_t_4220_, 0);
            lean_inc(v_elems_4233_);
            v_remainingCapacity_4234_ = lean_ctor_get(v_t_4220_, 1);
            lean_inc(v_remainingCapacity_4234_);
            lean_dec_ref_known(v_t_4220_, 2);
            v___x_4235_ = lean_apply_2(v_k_4221_, v_elems_4233_, v_remainingCapacity_4234_);
            return v___x_4235_;
        }
        _ => {
            let mut v_val_4236_: u64 = 0;
            let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
            v_val_4236_ = lean_ctor_get_uint64(v_t_4220_, 0 as u32);
            lean_dec_ref(v_t_4220_);
            v___x_4237_ = lean_box_uint64(v_val_4236_);
            v___x_4238_ = lean_apply_1(v_k_4221_, v___x_4237_);
            return v___x_4238_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim(
    mut v_motive_4239_: *mut LeanObject,
    mut v_ctorIdx_4240_: *mut LeanObject,
    mut v_t_4241_: *mut LeanObject,
    mut v_h_4242_: *mut LeanObject,
    mut v_k_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    v___x_4244_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4241_, v_k_4243_);
    return v___x_4244_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___boxed(
    mut v_motive_4245_: *mut LeanObject,
    mut v_ctorIdx_4246_: *mut LeanObject,
    mut v_t_4247_: *mut LeanObject,
    mut v_h_4248_: *mut LeanObject,
    mut v_k_4249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4250_: *mut LeanObject = core::ptr::null_mut();
    v_res_4250_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim(v_motive_4245_, v_ctorIdx_4246_, v_t_4247_, v_h_4248_, v_k_4249_);
    lean_dec(v_ctorIdx_4246_);
    return v_res_4250_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_arg_elim___redArg(
    mut v_t_4251_: *mut LeanObject,
    mut v_arg_4252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    v___x_4253_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4251_, v_arg_4252_);
    return v___x_4253_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_arg_elim(
    mut v_motive_4254_: *mut LeanObject,
    mut v_t_4255_: *mut LeanObject,
    mut v_h_4256_: *mut LeanObject,
    mut v_arg_4257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    v___x_4258_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4255_, v_arg_4257_);
    return v___x_4258_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint8_elim___redArg(
    mut v_t_4259_: *mut LeanObject,
    mut v_uint8_4260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    v___x_4261_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4259_, v_uint8_4260_);
    return v___x_4261_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint8_elim(
    mut v_motive_4262_: *mut LeanObject,
    mut v_t_4263_: *mut LeanObject,
    mut v_h_4264_: *mut LeanObject,
    mut v_uint8_4265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    v___x_4266_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4263_, v_uint8_4265_);
    return v___x_4266_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint16_elim___redArg(
    mut v_t_4267_: *mut LeanObject,
    mut v_uint16_4268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    v___x_4269_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4267_, v_uint16_4268_);
    return v___x_4269_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint16_elim(
    mut v_motive_4270_: *mut LeanObject,
    mut v_t_4271_: *mut LeanObject,
    mut v_h_4272_: *mut LeanObject,
    mut v_uint16_4273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    v___x_4274_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4271_, v_uint16_4273_);
    return v___x_4274_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint32_elim___redArg(
    mut v_t_4275_: *mut LeanObject,
    mut v_uint32_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    v___x_4277_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4275_, v_uint32_4276_);
    return v___x_4277_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint32_elim(
    mut v_motive_4278_: *mut LeanObject,
    mut v_t_4279_: *mut LeanObject,
    mut v_h_4280_: *mut LeanObject,
    mut v_uint32_4281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    v___x_4282_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4279_, v_uint32_4281_);
    return v___x_4282_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint64_elim___redArg(
    mut v_t_4283_: *mut LeanObject,
    mut v_uint64_4284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    v___x_4285_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4283_, v_uint64_4284_);
    return v___x_4285_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_uint64_elim(
    mut v_motive_4286_: *mut LeanObject,
    mut v_t_4287_: *mut LeanObject,
    mut v_h_4288_: *mut LeanObject,
    mut v_uint64_4289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    v___x_4290_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4287_, v_uint64_4289_);
    return v___x_4290_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_usize_elim___redArg(
    mut v_t_4291_: *mut LeanObject,
    mut v_usize_4292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    v___x_4293_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4291_, v_usize_4292_);
    return v___x_4293_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_usize_elim(
    mut v_motive_4294_: *mut LeanObject,
    mut v_t_4295_: *mut LeanObject,
    mut v_h_4296_: *mut LeanObject,
    mut v_usize_4297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    v___x_4298_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4295_, v_usize_4297_);
    return v___x_4298_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_arrayBuilder_elim___redArg(
    mut v_t_4299_: *mut LeanObject,
    mut v_arrayBuilder_4300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    v___x_4301_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4299_, v_arrayBuilder_4300_);
    return v___x_4301_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_arrayBuilder_elim(
    mut v_motive_4302_: *mut LeanObject,
    mut v_t_4303_: *mut LeanObject,
    mut v_h_4304_: *mut LeanObject,
    mut v_arrayBuilder_4305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    v___x_4306_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_SimpleGroundValue_ctorElim___redArg(v_t_4303_, v_arrayBuilder_4305_);
    return v___x_4306_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0_spec__1(
    mut v_msg_4311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    v___x_4312_ = l_Lean_Compiler_LCNF_instInhabitedSimpleGroundValue_default;
    v___x_4313_ = lean_panic_fn_borrowed(v___x_4312_, v_msg_4311_);
    return v___x_4313_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    v___x_4317_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__2;
    v___x_4318_ = lean_unsigned_to_nat(11);
    v___x_4319_ = lean_unsigned_to_nat(163);
    v___x_4320_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__1;
    v___x_4321_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__0;
    v___x_4322_ = l_mkPanicMessageWithDecl(
        v___x_4321_,
        v___x_4320_,
        v___x_4319_,
        v___x_4318_,
        v___x_4317_,
    );
    return v___x_4322_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0(
    mut v_a_4323_: *mut LeanObject,
    mut v_x_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4324_) == 0 {
                    v___x_4325_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___closed__3);
                    v___x_4326_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0_spec__1(v___x_4325_);
                    return v___x_4326_;
                } else {
                    v_key_4327_ = lean_ctor_get(v_x_4324_, 0);
                    v_value_4328_ = lean_ctor_get(v_x_4324_, 1);
                    v_tail_4329_ = lean_ctor_get(v_x_4324_, 2);
                    v___x_4330_ = l_Lean_instBEqFVarId_beq(v_key_4327_, v_a_4323_);
                    if v___x_4330_ == 0 {
                        v_x_4324_ = v_tail_4329_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4328_);
                        return v_value_4328_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0___boxed(
    mut v_a_4332_: *mut LeanObject,
    mut v_x_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4334_: *mut LeanObject = core::ptr::null_mut();
    v_res_4334_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0(v_a_4332_, v_x_4333_);
    lean_dec(v_x_4333_);
    lean_dec(v_a_4332_);
    return v_res_4334_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(
    mut v_m_4335_: *mut LeanObject,
    mut v_a_4336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: u64 = 0;
    let mut v___x_4340_: u64 = 0;
    let mut v___x_4341_: u64 = 0;
    let mut v_fold_4342_: u64 = 0;
    let mut v___x_4343_: u64 = 0;
    let mut v___x_4344_: u64 = 0;
    let mut v___x_4345_: u64 = 0;
    let mut v___x_4346_: usize = 0;
    let mut v___x_4347_: usize = 0;
    let mut v___x_4348_: usize = 0;
    let mut v___x_4349_: usize = 0;
    let mut v___x_4350_: usize = 0;
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_4337_ = lean_ctor_get(v_m_4335_, 1);
    v___x_4338_ = lean_array_get_size(v_buckets_4337_);
    v___x_4339_ = l_Lean_instHashableFVarId_hash(v_a_4336_);
    v___x_4340_ = 32u64;
    v___x_4341_ = lean_uint64_shift_right(v___x_4339_, v___x_4340_);
    v_fold_4342_ = lean_uint64_xor(v___x_4339_, v___x_4341_);
    v___x_4343_ = 16u64;
    v___x_4344_ = lean_uint64_shift_right(v_fold_4342_, v___x_4343_);
    v___x_4345_ = lean_uint64_xor(v_fold_4342_, v___x_4344_);
    v___x_4346_ = lean_uint64_to_usize(v___x_4345_);
    v___x_4347_ = lean_usize_of_nat(v___x_4338_);
    v___x_4348_ = 1usize;
    v___x_4349_ = lean_usize_sub(v___x_4347_, v___x_4348_);
    v___x_4350_ = lean_usize_land(v___x_4346_, v___x_4349_);
    v___x_4351_ = lean_array_uget_borrowed(v_buckets_4337_, v___x_4350_);
    v___x_4352_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0_spec__0(v_a_4336_, v___x_4351_);
    return v___x_4352_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0___boxed(
    mut v_m_4353_: *mut LeanObject,
    mut v_a_4354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4355_: *mut LeanObject = core::ptr::null_mut();
    v_res_4355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v_m_4353_, v_a_4354_);
    lean_dec(v_a_4354_);
    lean_dec_ref(v_m_4353_);
    return v_res_4355_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain___redArg(
    mut v_id_4356_: *mut LeanObject,
    mut v_info_4357_: *mut LeanObject,
    mut v_objArgs_4358_: *mut LeanObject,
    mut v_usizeArgs_4359_: *mut LeanObject,
    mut v_scalarArgs_4360_: *mut LeanObject,
    mut v_code_4361_: *mut LeanObject,
    mut v_a_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4367_: u8 = 0;
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v_fvarId_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4397_: u8 = 0;
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4401_: u16 = 0;
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: u16 = 0;
    let mut v___x_4408_: u16 = 0;
    let mut v___x_4409_: u8 = 0;
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4413_: u32 = 0;
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: u32 = 0;
    let mut v___x_4420_: u32 = 0;
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: u32 = 0;
    let mut v___x_4427_: u32 = 0;
    let mut v___x_4428_: u8 = 0;
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u32 = 0;
    let mut v___x_4434_: u32 = 0;
    let mut v___x_4435_: u8 = 0;
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4439_: u64 = 0;
    let mut v___x_4440_: u8 = 0;
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u64 = 0;
    let mut v___x_4446_: u64 = 0;
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: u64 = 0;
    let mut v___x_4453_: u64 = 0;
    let mut v___x_4454_: u8 = 0;
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: u64 = 0;
    let mut v___x_4460_: u64 = 0;
    let mut v___x_4461_: u8 = 0;
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: u64 = 0;
    let mut v___x_4467_: u64 = 0;
    let mut v___x_4468_: u8 = 0;
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: u64 = 0;
    let mut v___x_4474_: u64 = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: u64 = 0;
    let mut v___x_4481_: u64 = 0;
    let mut v___x_4482_: u8 = 0;
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: u64 = 0;
    let mut v___x_4488_: u64 = 0;
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4504_: u64 = 0;
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_4361_) {
                5 => {
                    v_fvarId_4364_ = lean_ctor_get(v_code_4361_, 0);
                    v_isSharedCheck_4379_ = (!lean_is_exclusive(v_code_4361_)) as u8;
                    if v_isSharedCheck_4379_ == 0 {
                        v___x_4366_ = v_code_4361_;
                        v_isShared_4367_ = v_isSharedCheck_4379_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_4364_);
                        lean_dec(v_code_4361_);
                        v___x_4366_ = lean_box(0);
                        v_isShared_4367_ = v_isSharedCheck_4379_;
                        state = 1;
                        continue;
                    }
                }
                9 => {
                    v_fvarId_4380_ = lean_ctor_get(v_code_4361_, 0);
                    lean_inc(v_fvarId_4380_);
                    v_i_4381_ = lean_ctor_get(v_code_4361_, 1);
                    lean_inc(v_i_4381_);
                    v_offset_4382_ = lean_ctor_get(v_code_4361_, 2);
                    lean_inc(v_offset_4382_);
                    v_y_4383_ = lean_ctor_get(v_code_4361_, 3);
                    lean_inc(v_y_4383_);
                    v_k_4384_ = lean_ctor_get(v_code_4361_, 5);
                    lean_inc_ref(v_k_4384_);
                    lean_dec_ref_known(v_code_4361_, 6);
                    v___x_4385_ = l_Lean_instBEqFVarId_beq(v_id_4356_, v_fvarId_4380_);
                    lean_dec(v_fvarId_4380_);
                    if v___x_4385_ == 0 {
                        lean_dec_ref(v_k_4384_);
                        lean_dec(v_y_4383_);
                        lean_dec(v_offset_4382_);
                        lean_dec(v_i_4381_);
                        lean_dec_ref(v_scalarArgs_4360_);
                        lean_dec_ref(v_usizeArgs_4359_);
                        lean_dec_ref(v_objArgs_4358_);
                        v___x_4386_ = lean_box(0);
                        v___x_4387_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4387_, 0, v___x_4386_);
                        return v___x_4387_;
                    } else {
                        v___x_4388_ = lean_st_ref_get(v_a_4362_);
                        v___x_4389_ = lean_array_get_size(v_objArgs_4358_);
                        v___x_4390_ = lean_nat_sub(v_i_4381_, v___x_4389_);
                        lean_dec(v_i_4381_);
                        v___x_4391_ = lean_array_get_size(v_usizeArgs_4359_);
                        v___x_4392_ = lean_nat_sub(v___x_4390_, v___x_4391_);
                        lean_dec(v___x_4390_);
                        v___x_4393_ = lean_unsigned_to_nat(8);
                        v___x_4394_ = lean_nat_mul(v___x_4392_, v___x_4393_);
                        lean_dec(v___x_4392_);
                        v___x_4395_ = lean_nat_add(v___x_4394_, v_offset_4382_);
                        lean_dec(v_offset_4382_);
                        lean_dec(v___x_4394_);
                        v___x_4396_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_4388_, v_y_4383_);
                        lean_dec(v_y_4383_);
                        lean_dec(v___x_4388_);
                        match lean_obj_tag(v___x_4396_) {
                            1 => {
                                v_val_4397_ = lean_ctor_get_uint8(v___x_4396_, 0 as u32);
                                lean_dec_ref_known(v___x_4396_, 0);
                                v___x_4398_ = lean_box((v_val_4397_) as usize);
                                v___x_4399_ =
                                    lean_array_set(v_scalarArgs_4360_, v___x_4395_, v___x_4398_);
                                lean_dec(v___x_4395_);
                                v_scalarArgs_4360_ = v___x_4399_;
                                v_code_4361_ = v_k_4384_;
                                state = 0;
                                continue;
                            }
                            2 => {
                                v_val_4401_ = lean_ctor_get_uint16(v___x_4396_, 0 as u32);
                                lean_dec_ref_known(v___x_4396_, 0);
                                v___x_4402_ = lean_uint16_to_uint8(v_val_4401_);
                                v___x_4403_ = lean_box((v___x_4402_) as usize);
                                v___x_4404_ =
                                    lean_array_set(v_scalarArgs_4360_, v___x_4395_, v___x_4403_);
                                v___x_4405_ = lean_unsigned_to_nat(1);
                                v___x_4406_ = lean_nat_add(v___x_4395_, v___x_4405_);
                                lean_dec(v___x_4395_);
                                v___x_4407_ = 8;
                                v___x_4408_ = lean_uint16_shift_right(v_val_4401_, v___x_4407_);
                                v___x_4409_ = lean_uint16_to_uint8(v___x_4408_);
                                v___x_4410_ = lean_box((v___x_4409_) as usize);
                                v___x_4411_ = lean_array_set(v___x_4404_, v___x_4406_, v___x_4410_);
                                lean_dec(v___x_4406_);
                                v_scalarArgs_4360_ = v___x_4411_;
                                v_code_4361_ = v_k_4384_;
                                state = 0;
                                continue;
                            }
                            3 => {
                                v_val_4413_ = lean_ctor_get_uint32(v___x_4396_, 0 as u32);
                                lean_dec_ref_known(v___x_4396_, 0);
                                v___x_4414_ = lean_uint32_to_uint8(v_val_4413_);
                                v___x_4415_ = lean_box((v___x_4414_) as usize);
                                v___x_4416_ =
                                    lean_array_set(v_scalarArgs_4360_, v___x_4395_, v___x_4415_);
                                v___x_4417_ = lean_unsigned_to_nat(1);
                                v___x_4418_ = lean_nat_add(v___x_4395_, v___x_4417_);
                                v___x_4419_ = 8;
                                v___x_4420_ = lean_uint32_shift_right(v_val_4413_, v___x_4419_);
                                v___x_4421_ = lean_uint32_to_uint8(v___x_4420_);
                                v___x_4422_ = lean_box((v___x_4421_) as usize);
                                v___x_4423_ = lean_array_set(v___x_4416_, v___x_4418_, v___x_4422_);
                                lean_dec(v___x_4418_);
                                v___x_4424_ = lean_unsigned_to_nat(2);
                                v___x_4425_ = lean_nat_add(v___x_4395_, v___x_4424_);
                                v___x_4426_ = 16;
                                v___x_4427_ = lean_uint32_shift_right(v_val_4413_, v___x_4426_);
                                v___x_4428_ = lean_uint32_to_uint8(v___x_4427_);
                                v___x_4429_ = lean_box((v___x_4428_) as usize);
                                v___x_4430_ = lean_array_set(v___x_4423_, v___x_4425_, v___x_4429_);
                                lean_dec(v___x_4425_);
                                v___x_4431_ = lean_unsigned_to_nat(3);
                                v___x_4432_ = lean_nat_add(v___x_4395_, v___x_4431_);
                                lean_dec(v___x_4395_);
                                v___x_4433_ = 24;
                                v___x_4434_ = lean_uint32_shift_right(v_val_4413_, v___x_4433_);
                                v___x_4435_ = lean_uint32_to_uint8(v___x_4434_);
                                v___x_4436_ = lean_box((v___x_4435_) as usize);
                                v___x_4437_ = lean_array_set(v___x_4430_, v___x_4432_, v___x_4436_);
                                lean_dec(v___x_4432_);
                                v_scalarArgs_4360_ = v___x_4437_;
                                v_code_4361_ = v_k_4384_;
                                state = 0;
                                continue;
                            }
                            4 => {
                                v_val_4439_ = lean_ctor_get_uint64(v___x_4396_, 0 as u32);
                                lean_dec_ref_known(v___x_4396_, 0);
                                v___x_4440_ = lean_uint64_to_uint8(v_val_4439_);
                                v___x_4441_ = lean_box((v___x_4440_) as usize);
                                v___x_4442_ =
                                    lean_array_set(v_scalarArgs_4360_, v___x_4395_, v___x_4441_);
                                v___x_4443_ = lean_unsigned_to_nat(1);
                                v___x_4444_ = lean_nat_add(v___x_4395_, v___x_4443_);
                                v___x_4445_ = 8u64;
                                v___x_4446_ = lean_uint64_shift_right(v_val_4439_, v___x_4445_);
                                v___x_4447_ = lean_uint64_to_uint8(v___x_4446_);
                                v___x_4448_ = lean_box((v___x_4447_) as usize);
                                v___x_4449_ = lean_array_set(v___x_4442_, v___x_4444_, v___x_4448_);
                                lean_dec(v___x_4444_);
                                v___x_4450_ = lean_unsigned_to_nat(2);
                                v___x_4451_ = lean_nat_add(v___x_4395_, v___x_4450_);
                                v___x_4452_ = 16u64;
                                v___x_4453_ = lean_uint64_shift_right(v_val_4439_, v___x_4452_);
                                v___x_4454_ = lean_uint64_to_uint8(v___x_4453_);
                                v___x_4455_ = lean_box((v___x_4454_) as usize);
                                v___x_4456_ = lean_array_set(v___x_4449_, v___x_4451_, v___x_4455_);
                                lean_dec(v___x_4451_);
                                v___x_4457_ = lean_unsigned_to_nat(3);
                                v___x_4458_ = lean_nat_add(v___x_4395_, v___x_4457_);
                                v___x_4459_ = 24u64;
                                v___x_4460_ = lean_uint64_shift_right(v_val_4439_, v___x_4459_);
                                v___x_4461_ = lean_uint64_to_uint8(v___x_4460_);
                                v___x_4462_ = lean_box((v___x_4461_) as usize);
                                v___x_4463_ = lean_array_set(v___x_4456_, v___x_4458_, v___x_4462_);
                                lean_dec(v___x_4458_);
                                v___x_4464_ = lean_unsigned_to_nat(4);
                                v___x_4465_ = lean_nat_add(v___x_4395_, v___x_4464_);
                                v___x_4466_ = 32u64;
                                v___x_4467_ = lean_uint64_shift_right(v_val_4439_, v___x_4466_);
                                v___x_4468_ = lean_uint64_to_uint8(v___x_4467_);
                                v___x_4469_ = lean_box((v___x_4468_) as usize);
                                v___x_4470_ = lean_array_set(v___x_4463_, v___x_4465_, v___x_4469_);
                                lean_dec(v___x_4465_);
                                v___x_4471_ = lean_unsigned_to_nat(5);
                                v___x_4472_ = lean_nat_add(v___x_4395_, v___x_4471_);
                                v___x_4473_ = 40u64;
                                v___x_4474_ = lean_uint64_shift_right(v_val_4439_, v___x_4473_);
                                v___x_4475_ = lean_uint64_to_uint8(v___x_4474_);
                                v___x_4476_ = lean_box((v___x_4475_) as usize);
                                v___x_4477_ = lean_array_set(v___x_4470_, v___x_4472_, v___x_4476_);
                                lean_dec(v___x_4472_);
                                v___x_4478_ = lean_unsigned_to_nat(6);
                                v___x_4479_ = lean_nat_add(v___x_4395_, v___x_4478_);
                                v___x_4480_ = 48u64;
                                v___x_4481_ = lean_uint64_shift_right(v_val_4439_, v___x_4480_);
                                v___x_4482_ = lean_uint64_to_uint8(v___x_4481_);
                                v___x_4483_ = lean_box((v___x_4482_) as usize);
                                v___x_4484_ = lean_array_set(v___x_4477_, v___x_4479_, v___x_4483_);
                                lean_dec(v___x_4479_);
                                v___x_4485_ = lean_unsigned_to_nat(7);
                                v___x_4486_ = lean_nat_add(v___x_4395_, v___x_4485_);
                                lean_dec(v___x_4395_);
                                v___x_4487_ = 56u64;
                                v___x_4488_ = lean_uint64_shift_right(v_val_4439_, v___x_4487_);
                                v___x_4489_ = lean_uint64_to_uint8(v___x_4488_);
                                v___x_4490_ = lean_box((v___x_4489_) as usize);
                                v___x_4491_ = lean_array_set(v___x_4484_, v___x_4486_, v___x_4490_);
                                lean_dec(v___x_4486_);
                                v_scalarArgs_4360_ = v___x_4491_;
                                v_code_4361_ = v_k_4384_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                lean_dec_ref(v___x_4396_);
                                lean_dec(v___x_4395_);
                                lean_dec_ref(v_k_4384_);
                                lean_dec_ref(v_scalarArgs_4360_);
                                lean_dec_ref(v_usizeArgs_4359_);
                                lean_dec_ref(v_objArgs_4358_);
                                v___x_4493_ = lean_box(0);
                                v___x_4494_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4494_, 0, v___x_4493_);
                                return v___x_4494_;
                            }
                        }
                    }
                }
                8 => {
                    v_fvarId_4495_ = lean_ctor_get(v_code_4361_, 0);
                    lean_inc(v_fvarId_4495_);
                    v_i_4496_ = lean_ctor_get(v_code_4361_, 1);
                    lean_inc(v_i_4496_);
                    v_y_4497_ = lean_ctor_get(v_code_4361_, 2);
                    lean_inc(v_y_4497_);
                    v_k_4498_ = lean_ctor_get(v_code_4361_, 3);
                    lean_inc_ref(v_k_4498_);
                    lean_dec_ref_known(v_code_4361_, 4);
                    v___x_4499_ = l_Lean_instBEqFVarId_beq(v_id_4356_, v_fvarId_4495_);
                    lean_dec(v_fvarId_4495_);
                    if v___x_4499_ == 0 {
                        lean_dec_ref(v_k_4498_);
                        lean_dec(v_y_4497_);
                        lean_dec(v_i_4496_);
                        lean_dec_ref(v_scalarArgs_4360_);
                        lean_dec_ref(v_usizeArgs_4359_);
                        lean_dec_ref(v_objArgs_4358_);
                        v___x_4500_ = lean_box(0);
                        v___x_4501_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4501_, 0, v___x_4500_);
                        return v___x_4501_;
                    } else {
                        v___x_4502_ = lean_st_ref_get(v_a_4362_);
                        v___x_4503_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_4502_, v_y_4497_);
                        lean_dec(v_y_4497_);
                        lean_dec(v___x_4502_);
                        if lean_obj_tag(v___x_4503_) == 5 {
                            v_val_4504_ = lean_ctor_get_uint64(v___x_4503_, 0 as u32);
                            lean_dec_ref_known(v___x_4503_, 0);
                            v___x_4505_ = lean_array_get_size(v_objArgs_4358_);
                            v___x_4506_ = lean_nat_sub(v_i_4496_, v___x_4505_);
                            lean_dec(v_i_4496_);
                            v___x_4507_ = lean_box_uint64(v_val_4504_);
                            v___x_4508_ =
                                lean_array_set(v_usizeArgs_4359_, v___x_4506_, v___x_4507_);
                            lean_dec(v___x_4506_);
                            v_usizeArgs_4359_ = v___x_4508_;
                            v_code_4361_ = v_k_4498_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v___x_4503_);
                            lean_dec_ref(v_k_4498_);
                            lean_dec(v_i_4496_);
                            lean_dec_ref(v_scalarArgs_4360_);
                            lean_dec_ref(v_usizeArgs_4359_);
                            lean_dec_ref(v_objArgs_4358_);
                            v___x_4510_ = lean_box(0);
                            v___x_4511_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4511_, 0, v___x_4510_);
                            return v___x_4511_;
                        }
                    }
                }
                _ => {
                    lean_dec_ref(v_code_4361_);
                    lean_dec_ref(v_scalarArgs_4360_);
                    lean_dec_ref(v_usizeArgs_4359_);
                    lean_dec_ref(v_objArgs_4358_);
                    v___x_4512_ = lean_box(0);
                    v___x_4513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4513_, 0, v___x_4512_);
                    return v___x_4513_;
                }
            },
            1 => {
                v___x_4368_ = l_Lean_instBEqFVarId_beq(v_id_4356_, v_fvarId_4364_);
                lean_dec(v_fvarId_4364_);
                if v___x_4368_ == 0 {
                    lean_dec_ref(v_scalarArgs_4360_);
                    lean_dec_ref(v_usizeArgs_4359_);
                    lean_dec_ref(v_objArgs_4358_);
                    v___x_4369_ = lean_box(0);
                    if v_isShared_4367_ == 0 {
                        lean_ctor_set_tag(v___x_4366_, 0);
                        lean_ctor_set(v___x_4366_, 0, v___x_4369_);
                        v___x_4371_ = v___x_4366_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4369_);
                        v___x_4371_ = v_reuseFailAlloc_4372_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_cidx_4373_ = lean_ctor_get(v_info_4357_, 1);
                    lean_inc(v_cidx_4373_);
                    v___x_4374_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_4374_, 0, v_cidx_4373_);
                    lean_ctor_set(v___x_4374_, 1, v_objArgs_4358_);
                    lean_ctor_set(v___x_4374_, 2, v_usizeArgs_4359_);
                    lean_ctor_set(v___x_4374_, 3, v_scalarArgs_4360_);
                    if v_isShared_4367_ == 0 {
                        lean_ctor_set_tag(v___x_4366_, 1);
                        lean_ctor_set(v___x_4366_, 0, v___x_4374_);
                        v___x_4376_ = v___x_4366_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4374_);
                        v___x_4376_ = v_reuseFailAlloc_4378_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4371_;
            }
            3 => {
                v___x_4377_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4377_, 0, v___x_4376_);
                return v___x_4377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain___redArg___boxed(
    mut v_id_4514_: *mut LeanObject,
    mut v_info_4515_: *mut LeanObject,
    mut v_objArgs_4516_: *mut LeanObject,
    mut v_usizeArgs_4517_: *mut LeanObject,
    mut v_scalarArgs_4518_: *mut LeanObject,
    mut v_code_4519_: *mut LeanObject,
    mut v_a_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4522_: *mut LeanObject = core::ptr::null_mut();
    v_res_4522_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain___redArg(v_id_4514_, v_info_4515_, v_objArgs_4516_, v_usizeArgs_4517_, v_scalarArgs_4518_, v_code_4519_, v_a_4520_);
    lean_dec(v_a_4520_);
    lean_dec_ref(v_info_4515_);
    lean_dec(v_id_4514_);
    return v_res_4522_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain(
    mut v_id_4523_: *mut LeanObject,
    mut v_info_4524_: *mut LeanObject,
    mut v_objArgs_4525_: *mut LeanObject,
    mut v_usizeArgs_4526_: *mut LeanObject,
    mut v_scalarArgs_4527_: *mut LeanObject,
    mut v_code_4528_: *mut LeanObject,
    mut v_a_4529_: *mut LeanObject,
    mut v_a_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
    mut v_a_4532_: *mut LeanObject,
    mut v_a_4533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    v___x_4535_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain___redArg(v_id_4523_, v_info_4524_, v_objArgs_4525_, v_usizeArgs_4526_, v_scalarArgs_4527_, v_code_4528_, v_a_4529_);
    return v___x_4535_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain___boxed(
    mut v_id_4536_: *mut LeanObject,
    mut v_info_4537_: *mut LeanObject,
    mut v_objArgs_4538_: *mut LeanObject,
    mut v_usizeArgs_4539_: *mut LeanObject,
    mut v_scalarArgs_4540_: *mut LeanObject,
    mut v_code_4541_: *mut LeanObject,
    mut v_a_4542_: *mut LeanObject,
    mut v_a_4543_: *mut LeanObject,
    mut v_a_4544_: *mut LeanObject,
    mut v_a_4545_: *mut LeanObject,
    mut v_a_4546_: *mut LeanObject,
    mut v_a_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4548_: *mut LeanObject = core::ptr::null_mut();
    v_res_4548_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain(v_id_4536_, v_info_4537_, v_objArgs_4538_, v_usizeArgs_4539_, v_scalarArgs_4540_, v_code_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
    lean_dec(v_a_4546_);
    lean_dec_ref(v_a_4545_);
    lean_dec(v_a_4544_);
    lean_dec_ref(v_a_4543_);
    lean_dec(v_a_4542_);
    lean_dec_ref(v_info_4537_);
    lean_dec(v_id_4536_);
    return v_res_4548_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg(
    mut v_arg_4551_: *mut LeanObject,
    mut v_a_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_arg_4551_) == 0 {
                    v___x_4554_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg___closed__0;
                    v___x_4555_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4555_, 0, v___x_4554_);
                    return v___x_4555_;
                } else {
                    v_fvarId_4556_ = lean_ctor_get(v_arg_4551_, 0);
                    v_isSharedCheck_4577_ = (!lean_is_exclusive(v_arg_4551_)) as u8;
                    if v_isSharedCheck_4577_ == 0 {
                        v___x_4558_ = v_arg_4551_;
                        v_isShared_4559_ = v_isSharedCheck_4577_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_4556_);
                        lean_dec(v_arg_4551_);
                        v___x_4558_ = lean_box(0);
                        v_isShared_4559_ = v_isSharedCheck_4577_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4560_ = lean_st_ref_get(v_a_4552_);
                v___x_4561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_4560_, v_fvarId_4556_);
                lean_dec(v_fvarId_4556_);
                lean_dec(v___x_4560_);
                if lean_obj_tag(v___x_4561_) == 0 {
                    v_arg_4562_ = lean_ctor_get(v___x_4561_, 0);
                    v_isSharedCheck_4572_ = (!lean_is_exclusive(v___x_4561_)) as u8;
                    if v_isSharedCheck_4572_ == 0 {
                        v___x_4564_ = v___x_4561_;
                        v_isShared_4565_ = v_isSharedCheck_4572_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_arg_4562_);
                        lean_dec(v___x_4561_);
                        v___x_4564_ = lean_box(0);
                        v_isShared_4565_ = v_isSharedCheck_4572_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4561_);
                    v___x_4573_ = lean_box(0);
                    if v_isShared_4559_ == 0 {
                        lean_ctor_set_tag(v___x_4558_, 0);
                        lean_ctor_set(v___x_4558_, 0, v___x_4573_);
                        v___x_4575_ = v___x_4558_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4576_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4573_);
                        v___x_4575_ = v_reuseFailAlloc_4576_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4565_ == 0 {
                    lean_ctor_set_tag(v___x_4564_, 1);
                    v___x_4567_ = v___x_4564_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_arg_4562_);
                    v___x_4567_ = v_reuseFailAlloc_4571_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4559_ == 0 {
                    lean_ctor_set_tag(v___x_4558_, 0);
                    lean_ctor_set(v___x_4558_, 0, v___x_4567_);
                    v___x_4569_ = v___x_4558_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4570_, 0, v___x_4567_);
                    v___x_4569_ = v_reuseFailAlloc_4570_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4569_;
            }
            5 => {
                return v___x_4575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg___boxed(
    mut v_arg_4578_: *mut LeanObject,
    mut v_a_4579_: *mut LeanObject,
    mut v_a_4580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4581_: *mut LeanObject = core::ptr::null_mut();
    v_res_4581_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg(v_arg_4578_, v_a_4579_);
    lean_dec(v_a_4579_);
    return v_res_4581_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg(
    mut v_arg_4582_: *mut LeanObject,
    mut v_a_4583_: *mut LeanObject,
    mut v_a_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
    mut v_a_4586_: *mut LeanObject,
    mut v_a_4587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    v___x_4589_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg(v_arg_4582_, v_a_4583_);
    return v___x_4589_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___boxed(
    mut v_arg_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
    mut v_a_4592_: *mut LeanObject,
    mut v_a_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
    mut v_a_4595_: *mut LeanObject,
    mut v_a_4596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4597_: *mut LeanObject = core::ptr::null_mut();
    v_res_4597_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg(v_arg_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_);
    lean_dec(v_a_4595_);
    lean_dec_ref(v_a_4594_);
    lean_dec(v_a_4593_);
    lean_dec_ref(v_a_4592_);
    lean_dec(v_a_4591_);
    return v_res_4597_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0___redArg(
    mut v_sz_4598_: usize,
    mut v_i_4599_: usize,
    mut v_bs_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4603_: u8 = 0;
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4611_: u8 = 0;
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: usize = 0;
    let mut v___x_4620_: usize = 0;
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4623_: u8 = 0;
    let mut v_a_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4627_: u8 = 0;
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4603_ = lean_usize_dec_lt(v_i_4599_, v_sz_4598_);
                if v___x_4603_ == 0 {
                    v___x_4604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4604_, 0, v_bs_4600_);
                    v___x_4605_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4605_, 0, v___x_4604_);
                    return v___x_4605_;
                } else {
                    v_v_4606_ = lean_array_uget_borrowed(v_bs_4600_, v_i_4599_);
                    lean_inc(v_v_4606_);
                    v___x_4607_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg(v_v_4606_, v___y_4601_);
                    if lean_obj_tag(v___x_4607_) == 0 {
                        v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
                        v_isSharedCheck_4623_ = (!lean_is_exclusive(v___x_4607_)) as u8;
                        if v_isSharedCheck_4623_ == 0 {
                            v___x_4610_ = v___x_4607_;
                            v_isShared_4611_ = v_isSharedCheck_4623_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4608_);
                            lean_dec(v___x_4607_);
                            v___x_4610_ = lean_box(0);
                            v_isShared_4611_ = v_isSharedCheck_4623_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_bs_4600_);
                        v_a_4624_ = lean_ctor_get(v___x_4607_, 0);
                        v_isSharedCheck_4631_ = (!lean_is_exclusive(v___x_4607_)) as u8;
                        if v_isSharedCheck_4631_ == 0 {
                            v___x_4626_ = v___x_4607_;
                            v_isShared_4627_ = v_isSharedCheck_4631_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4624_);
                            lean_dec(v___x_4607_);
                            v___x_4626_ = lean_box(0);
                            v_isShared_4627_ = v_isSharedCheck_4631_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4608_) == 0 {
                    lean_dec_ref(v_bs_4600_);
                    v___x_4612_ = lean_box(0);
                    if v_isShared_4611_ == 0 {
                        lean_ctor_set(v___x_4610_, 0, v___x_4612_);
                        v___x_4614_ = v___x_4610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
                        v___x_4614_ = v_reuseFailAlloc_4615_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4610_);
                    v_val_4616_ = lean_ctor_get(v_a_4608_, 0);
                    lean_inc(v_val_4616_);
                    lean_dec_ref_known(v_a_4608_, 1);
                    v___x_4617_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4618_ = lean_array_uset(v_bs_4600_, v_i_4599_, v___x_4617_);
                    v___x_4619_ = 1usize;
                    v___x_4620_ = lean_usize_add(v_i_4599_, v___x_4619_);
                    v___x_4621_ = lean_array_uset(v_bs_x27_4618_, v_i_4599_, v_val_4616_);
                    v_i_4599_ = v___x_4620_;
                    v_bs_4600_ = v___x_4621_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_4614_;
            }
            3 => {
                if v_isShared_4627_ == 0 {
                    v___x_4629_ = v___x_4626_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
                    v___x_4629_ = v_reuseFailAlloc_4630_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0___redArg___boxed(
    mut v_sz_4632_: *mut LeanObject,
    mut v_i_4633_: *mut LeanObject,
    mut v_bs_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4637_: usize = 0;
    let mut v_i_boxed_4638_: usize = 0;
    let mut v_res_4639_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4637_ = lean_unbox_usize(v_sz_4632_);
    lean_dec(v_sz_4632_);
    v_i_boxed_4638_ = lean_unbox_usize(v_i_4633_);
    lean_dec(v_i_4633_);
    v_res_4639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0___redArg(v_sz_boxed_4637_, v_i_boxed_4638_, v_bs_4634_, v___y_4635_);
    lean_dec(v___y_4635_);
    return v_res_4639_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs(
    mut v_args_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
    mut v_a_4642_: *mut LeanObject,
    mut v_a_4643_: *mut LeanObject,
    mut v_a_4644_: *mut LeanObject,
    mut v_a_4645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_4647_: usize = 0;
    let mut v___x_4648_: usize = 0;
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    v_sz_4647_ = lean_array_size(v_args_4640_);
    v___x_4648_ = 0usize;
    v___x_4649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0___redArg(v_sz_4647_, v___x_4648_, v_args_4640_, v_a_4641_);
    return v___x_4649_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs___boxed(
    mut v_args_4650_: *mut LeanObject,
    mut v_a_4651_: *mut LeanObject,
    mut v_a_4652_: *mut LeanObject,
    mut v_a_4653_: *mut LeanObject,
    mut v_a_4654_: *mut LeanObject,
    mut v_a_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4657_: *mut LeanObject = core::ptr::null_mut();
    v_res_4657_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs(v_args_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_);
    lean_dec(v_a_4655_);
    lean_dec_ref(v_a_4654_);
    lean_dec(v_a_4653_);
    lean_dec_ref(v_a_4652_);
    lean_dec(v_a_4651_);
    return v_res_4657_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0(
    mut v_sz_4658_: usize,
    mut v_i_4659_: usize,
    mut v_bs_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0___redArg(v_sz_4658_, v_i_4659_, v_bs_4660_, v___y_4661_);
    return v___x_4667_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0___boxed(
    mut v_sz_4668_: *mut LeanObject,
    mut v_i_4669_: *mut LeanObject,
    mut v_bs_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4677_: usize = 0;
    let mut v_i_boxed_4678_: usize = 0;
    let mut v_res_4679_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4677_ = lean_unbox_usize(v_sz_4668_);
    lean_dec(v_sz_4668_);
    v_i_boxed_4678_ = lean_unbox_usize(v_i_4669_);
    lean_dec(v_i_4669_);
    v_res_4679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs_spec__0(v_sz_boxed_4677_, v_i_boxed_4678_, v_bs_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
    lean_dec(v___y_4675_);
    lean_dec_ref(v___y_4674_);
    lean_dec(v___y_4673_);
    lean_dec_ref(v___y_4672_);
    lean_dec(v___y_4671_);
    return v_res_4679_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg(
    mut v_id_4684_: *mut LeanObject,
    mut v_val_4685_: *mut LeanObject,
    mut v_a_4686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    v___x_4688_ = lean_st_ref_take(v_a_4686_);
    v___x_4689_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__0;
    v___x_4690_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__1;
    v___x_4691_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___x_4689_,
        v___x_4690_,
        v___x_4688_,
        v_id_4684_,
        v_val_4685_,
    );
    v___x_4692_ = lean_st_ref_set(v_a_4686_, v___x_4691_);
    v___x_4693_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__2;
    v___x_4694_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4694_, 0, v___x_4693_);
    return v___x_4694_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___boxed(
    mut v_id_4695_: *mut LeanObject,
    mut v_val_4696_: *mut LeanObject,
    mut v_a_4697_: *mut LeanObject,
    mut v_a_4698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4699_: *mut LeanObject = core::ptr::null_mut();
    v_res_4699_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg(v_id_4695_, v_val_4696_, v_a_4697_);
    lean_dec(v_a_4697_);
    return v_res_4699_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record(
    mut v_id_4700_: *mut LeanObject,
    mut v_val_4701_: *mut LeanObject,
    mut v_a_4702_: *mut LeanObject,
    mut v_a_4703_: *mut LeanObject,
    mut v_a_4704_: *mut LeanObject,
    mut v_a_4705_: *mut LeanObject,
    mut v_a_4706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    v___x_4708_ = lean_st_ref_take(v_a_4702_);
    v___x_4709_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__0;
    v___x_4710_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__1;
    v___x_4711_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___x_4709_,
        v___x_4710_,
        v___x_4708_,
        v_id_4700_,
        v_val_4701_,
    );
    v___x_4712_ = lean_st_ref_set(v_a_4702_, v___x_4711_);
    v___x_4713_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___redArg___closed__2;
    v___x_4714_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4714_, 0, v___x_4713_);
    return v___x_4714_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record___boxed(
    mut v_id_4715_: *mut LeanObject,
    mut v_val_4716_: *mut LeanObject,
    mut v_a_4717_: *mut LeanObject,
    mut v_a_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
    mut v_a_4722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4723_: *mut LeanObject = core::ptr::null_mut();
    v_res_4723_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_record(v_id_4715_, v_val_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_, v_a_4721_);
    lean_dec(v_a_4721_);
    lean_dec_ref(v_a_4720_);
    lean_dec(v_a_4719_);
    lean_dec_ref(v_a_4718_);
    lean_dec(v_a_4717_);
    return v_res_4723_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg___redArg(
    mut v_arg_4724_: *mut LeanObject,
    mut v_a_4725_: *mut LeanObject,
    mut v_a_4726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4734_: u8 = 0;
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4750_: u8 = 0;
    let mut v_data_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4754_: u8 = 0;
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut v_isSharedCheck_4764_: u8 = 0;
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_arg_4724_) == 1 {
                    v_fvarId_4731_ = lean_ctor_get(v_arg_4724_, 0);
                    v_isSharedCheck_4764_ = (!lean_is_exclusive(v_arg_4724_)) as u8;
                    if v_isSharedCheck_4764_ == 0 {
                        v___x_4733_ = v_arg_4724_;
                        v_isShared_4734_ = v_isSharedCheck_4764_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fvarId_4731_);
                        lean_dec(v_arg_4724_);
                        v___x_4733_ = lean_box(0);
                        v_isShared_4734_ = v_isSharedCheck_4764_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_arg_4724_);
                    v___x_4765_ = lean_box(0);
                    v___x_4766_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4766_, 0, v___x_4765_);
                    return v___x_4766_;
                }
            }
            1 => {
                v___x_4729_ = lean_box(0);
                v___x_4730_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4730_, 0, v___x_4729_);
                return v___x_4730_;
            }
            2 => {
                v___x_4735_ = lean_st_ref_get(v_a_4725_);
                v___x_4741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_4735_, v_fvarId_4731_);
                lean_dec(v_fvarId_4731_);
                lean_dec(v___x_4735_);
                if lean_obj_tag(v___x_4741_) == 0 {
                    v_arg_4742_ = lean_ctor_get(v___x_4741_, 0);
                    lean_inc_ref(v_arg_4742_);
                    lean_dec_ref_known(v___x_4741_, 1);
                    if lean_obj_tag(v_arg_4742_) == 1 {
                        lean_del_object(v___x_4733_);
                        v_n_4743_ = lean_ctor_get(v_arg_4742_, 0);
                        lean_inc_n(v_n_4743_, 2);
                        lean_dec_ref_known(v_arg_4742_, 1);
                        v___x_4744_ = lean_st_ref_get(v_a_4726_);
                        v_env_4745_ = lean_ctor_get(v___x_4744_, 0);
                        lean_inc_ref(v_env_4745_);
                        lean_dec(v___x_4744_);
                        v___x_4746_ = l_Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs(
                            v_env_4745_,
                            v_n_4743_,
                        );
                        if lean_obj_tag(v___x_4746_) == 1 {
                            v_val_4747_ = lean_ctor_get(v___x_4746_, 0);
                            v_isSharedCheck_4763_ = (!lean_is_exclusive(v___x_4746_)) as u8;
                            if v_isSharedCheck_4763_ == 0 {
                                v___x_4749_ = v___x_4746_;
                                v_isShared_4750_ = v_isSharedCheck_4763_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_val_4747_);
                                lean_dec(v___x_4746_);
                                v___x_4749_ = lean_box(0);
                                v_isShared_4750_ = v_isSharedCheck_4763_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_4746_);
                            lean_dec(v_n_4743_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_4742_);
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_4741_);
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4737_ = lean_box(0);
                if v_isShared_4734_ == 0 {
                    lean_ctor_set_tag(v___x_4733_, 0);
                    lean_ctor_set(v___x_4733_, 0, v___x_4737_);
                    v___x_4739_ = v___x_4733_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4737_);
                    v___x_4739_ = v_reuseFailAlloc_4740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4739_;
            }
            5 => {
                if lean_obj_tag(v_val_4747_) == 1 {
                    v_data_4751_ = lean_ctor_get(v_val_4747_, 0);
                    v_isSharedCheck_4762_ = (!lean_is_exclusive(v_val_4747_)) as u8;
                    if v_isSharedCheck_4762_ == 0 {
                        v___x_4753_ = v_val_4747_;
                        v_isShared_4754_ = v_isSharedCheck_4762_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_data_4751_);
                        lean_dec(v_val_4747_);
                        v___x_4753_ = lean_box(0);
                        v_isShared_4754_ = v_isSharedCheck_4762_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4749_);
                    lean_dec(v_val_4747_);
                    lean_dec(v_n_4743_);
                    state = 1;
                    continue;
                }
            }
            6 => {
                v___x_4755_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4755_, 0, v_n_4743_);
                lean_ctor_set(v___x_4755_, 1, v_data_4751_);
                if v_isShared_4750_ == 0 {
                    lean_ctor_set(v___x_4749_, 0, v___x_4755_);
                    v___x_4757_ = v___x_4749_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4761_, 0, v___x_4755_);
                    v___x_4757_ = v_reuseFailAlloc_4761_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4754_ == 0 {
                    lean_ctor_set_tag(v___x_4753_, 0);
                    lean_ctor_set(v___x_4753_, 0, v___x_4757_);
                    v___x_4759_ = v___x_4753_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4757_);
                    v___x_4759_ = v_reuseFailAlloc_4760_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg___redArg___boxed(
    mut v_arg_4767_: *mut LeanObject,
    mut v_a_4768_: *mut LeanObject,
    mut v_a_4769_: *mut LeanObject,
    mut v_a_4770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4771_: *mut LeanObject = core::ptr::null_mut();
    v_res_4771_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg___redArg(v_arg_4767_, v_a_4768_, v_a_4769_);
    lean_dec(v_a_4769_);
    lean_dec(v_a_4768_);
    return v_res_4771_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg(
    mut v_arg_4772_: *mut LeanObject,
    mut v_a_4773_: *mut LeanObject,
    mut v_a_4774_: *mut LeanObject,
    mut v_a_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
    mut v_a_4777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    v___x_4779_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg___redArg(v_arg_4772_, v_a_4773_, v_a_4777_);
    return v___x_4779_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg___boxed(
    mut v_arg_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_a_4782_: *mut LeanObject,
    mut v_a_4783_: *mut LeanObject,
    mut v_a_4784_: *mut LeanObject,
    mut v_a_4785_: *mut LeanObject,
    mut v_a_4786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4787_: *mut LeanObject = core::ptr::null_mut();
    v_res_4787_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg(v_arg_4780_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
    lean_dec(v_a_4785_);
    lean_dec_ref(v_a_4784_);
    lean_dec(v_a_4783_);
    lean_dec_ref(v_a_4782_);
    lean_dec(v_a_4781_);
    return v_res_4787_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral___redArg(
    mut v_arg_4788_: *mut LeanObject,
    mut v_a_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v_data_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4812_: u8 = 0;
    let mut v_isSharedCheck_4813_: u8 = 0;
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_arg_4788_) == 1 {
                    v_n_4794_ = lean_ctor_get(v_arg_4788_, 0);
                    lean_inc(v_n_4794_);
                    lean_dec_ref_known(v_arg_4788_, 1);
                    v___x_4795_ = lean_st_ref_get(v_a_4789_);
                    v_env_4796_ = lean_ctor_get(v___x_4795_, 0);
                    lean_inc_ref(v_env_4796_);
                    lean_dec(v___x_4795_);
                    v___x_4797_ = l_Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs(
                        v_env_4796_,
                        v_n_4794_,
                    );
                    if lean_obj_tag(v___x_4797_) == 1 {
                        v_val_4798_ = lean_ctor_get(v___x_4797_, 0);
                        v_isSharedCheck_4813_ = (!lean_is_exclusive(v___x_4797_)) as u8;
                        if v_isSharedCheck_4813_ == 0 {
                            v___x_4800_ = v___x_4797_;
                            v_isShared_4801_ = v_isSharedCheck_4813_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_4798_);
                            lean_dec(v___x_4797_);
                            v___x_4800_ = lean_box(0);
                            v_isShared_4801_ = v_isSharedCheck_4813_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4797_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_arg_4788_);
                    v___x_4814_ = lean_box(0);
                    v___x_4815_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4815_, 0, v___x_4814_);
                    return v___x_4815_;
                }
            }
            1 => {
                v___x_4792_ = lean_box(0);
                v___x_4793_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4793_, 0, v___x_4792_);
                return v___x_4793_;
            }
            2 => {
                if lean_obj_tag(v_val_4798_) == 1 {
                    v_data_4802_ = lean_ctor_get(v_val_4798_, 0);
                    v_isSharedCheck_4812_ = (!lean_is_exclusive(v_val_4798_)) as u8;
                    if v_isSharedCheck_4812_ == 0 {
                        v___x_4804_ = v_val_4798_;
                        v_isShared_4805_ = v_isSharedCheck_4812_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_data_4802_);
                        lean_dec(v_val_4798_);
                        v___x_4804_ = lean_box(0);
                        v_isShared_4805_ = v_isSharedCheck_4812_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4800_);
                    lean_dec(v_val_4798_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4801_ == 0 {
                    lean_ctor_set(v___x_4800_, 0, v_data_4802_);
                    v___x_4807_ = v___x_4800_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_data_4802_);
                    v___x_4807_ = v_reuseFailAlloc_4811_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4805_ == 0 {
                    lean_ctor_set_tag(v___x_4804_, 0);
                    lean_ctor_set(v___x_4804_, 0, v___x_4807_);
                    v___x_4809_ = v___x_4804_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4807_);
                    v___x_4809_ = v_reuseFailAlloc_4810_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4809_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral___redArg___boxed(
    mut v_arg_4816_: *mut LeanObject,
    mut v_a_4817_: *mut LeanObject,
    mut v_a_4818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4819_: *mut LeanObject = core::ptr::null_mut();
    v_res_4819_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral___redArg(v_arg_4816_, v_a_4817_);
    lean_dec(v_a_4817_);
    return v_res_4819_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral(
    mut v_arg_4820_: *mut LeanObject,
    mut v_a_4821_: *mut LeanObject,
    mut v_a_4822_: *mut LeanObject,
    mut v_a_4823_: *mut LeanObject,
    mut v_a_4824_: *mut LeanObject,
    mut v_a_4825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    v___x_4827_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral___redArg(v_arg_4820_, v_a_4825_);
    return v___x_4827_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral___boxed(
    mut v_arg_4828_: *mut LeanObject,
    mut v_a_4829_: *mut LeanObject,
    mut v_a_4830_: *mut LeanObject,
    mut v_a_4831_: *mut LeanObject,
    mut v_a_4832_: *mut LeanObject,
    mut v_a_4833_: *mut LeanObject,
    mut v_a_4834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4835_: *mut LeanObject = core::ptr::null_mut();
    v_res_4835_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral(v_arg_4828_, v_a_4829_, v_a_4830_, v_a_4831_, v_a_4832_, v_a_4833_);
    lean_dec(v_a_4833_);
    lean_dec_ref(v_a_4832_);
    lean_dec(v_a_4831_);
    lean_dec_ref(v_a_4830_);
    lean_dec(v_a_4829_);
    return v_res_4835_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0___redArg(
    mut v_as_4836_: *mut LeanObject,
    mut v_i_4837_: usize,
    mut v_stop_4838_: usize,
    mut v_b_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4842_: u8 = 0;
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4850_: u8 = 0;
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: usize = 0;
    let mut v___x_4858_: usize = 0;
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_a_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4842_ = lean_usize_dec_eq(v_i_4837_, v_stop_4838_);
                if v___x_4842_ == 0 {
                    v___x_4843_ = lean_array_uget_borrowed(v_as_4836_, v_i_4837_);
                    v_fst_4844_ = lean_ctor_get(v___x_4843_, 0);
                    lean_inc(v_fst_4844_);
                    v___x_4845_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4845_, 0, v_fst_4844_);
                    v___x_4846_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral___redArg(v___x_4845_, v___y_4840_);
                    if lean_obj_tag(v___x_4846_) == 0 {
                        v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
                        v_isSharedCheck_4860_ = (!lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4860_ == 0 {
                            v___x_4849_ = v___x_4846_;
                            v_isShared_4850_ = v_isSharedCheck_4860_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4847_);
                            lean_dec(v___x_4846_);
                            v___x_4849_ = lean_box(0);
                            v_isShared_4850_ = v_isSharedCheck_4860_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_b_4839_);
                        v_a_4861_ = lean_ctor_get(v___x_4846_, 0);
                        v_isSharedCheck_4868_ = (!lean_is_exclusive(v___x_4846_)) as u8;
                        if v_isSharedCheck_4868_ == 0 {
                            v___x_4863_ = v___x_4846_;
                            v_isShared_4864_ = v_isSharedCheck_4868_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4861_);
                            lean_dec(v___x_4846_);
                            v___x_4863_ = lean_box(0);
                            v_isShared_4864_ = v_isSharedCheck_4868_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_4869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4869_, 0, v_b_4839_);
                    v___x_4870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4870_, 0, v___x_4869_);
                    return v___x_4870_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_4847_) == 0 {
                    lean_dec(v_b_4839_);
                    v___x_4851_ = lean_box(0);
                    if v_isShared_4850_ == 0 {
                        lean_ctor_set(v___x_4849_, 0, v___x_4851_);
                        v___x_4853_ = v___x_4849_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4854_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4851_);
                        v___x_4853_ = v_reuseFailAlloc_4854_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4849_);
                    v_val_4855_ = lean_ctor_get(v_a_4847_, 0);
                    lean_inc(v_val_4855_);
                    lean_dec_ref_known(v_a_4847_, 1);
                    v___x_4856_ = l_Lean_Name_str___override(v_b_4839_, v_val_4855_);
                    v___x_4857_ = 1usize;
                    v___x_4858_ = lean_usize_add(v_i_4837_, v___x_4857_);
                    v_i_4837_ = v___x_4858_;
                    v_b_4839_ = v___x_4856_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_4853_;
            }
            3 => {
                if v_isShared_4864_ == 0 {
                    v___x_4866_ = v___x_4863_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
                    v___x_4866_ = v_reuseFailAlloc_4867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0___redArg___boxed(
    mut v_as_4871_: *mut LeanObject,
    mut v_i_4872_: *mut LeanObject,
    mut v_stop_4873_: *mut LeanObject,
    mut v_b_4874_: *mut LeanObject,
    mut v___y_4875_: *mut LeanObject,
    mut v___y_4876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4877_: usize = 0;
    let mut v_stop_boxed_4878_: usize = 0;
    let mut v_res_4879_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4877_ = lean_unbox_usize(v_i_4872_);
    lean_dec(v_i_4872_);
    v_stop_boxed_4878_ = lean_unbox_usize(v_stop_4873_);
    lean_dec(v_stop_4873_);
    v_res_4879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0___redArg(v_as_4871_, v_i_boxed_4877_, v_stop_boxed_4878_, v_b_4874_, v___y_4875_);
    lean_dec(v___y_4875_);
    lean_dec_ref(v_as_4871_);
    return v_res_4879_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral(
    mut v_arg_4882_: *mut LeanObject,
    mut v_a_4883_: *mut LeanObject,
    mut v_a_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
    mut v_a_4886_: *mut LeanObject,
    mut v_a_4887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4898_: u8 = 0;
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: u8 = 0;
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4905_: u8 = 0;
    let mut v_n_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_objArgs_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: u8 = 0;
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: u8 = 0;
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: u8 = 0;
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v_val_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4931_: u8 = 0;
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_isSharedCheck_4940_: u8 = 0;
    let mut v_unused_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4955_: u8 = 0;
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4963_: u8 = 0;
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4971_: u8 = 0;
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut v_a_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4976_: u8 = 0;
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_args_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: u8 = 0;
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: u8 = 0;
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: usize = 0;
    let mut v___x_4999_: usize = 0;
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: usize = 0;
    let mut v___x_5002_: usize = 0;
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_arg_4882_) {
                0 => {
                    v_val_4895_ = lean_ctor_get(v_arg_4882_, 0);
                    v_isSharedCheck_4905_ = (!lean_is_exclusive(v_arg_4882_)) as u8;
                    if v_isSharedCheck_4905_ == 0 {
                        v___x_4897_ = v_arg_4882_;
                        v_isShared_4898_ = v_isSharedCheck_4905_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_4895_);
                        lean_dec(v_arg_4882_);
                        v___x_4897_ = lean_box(0);
                        v_isShared_4898_ = v_isSharedCheck_4905_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_n_4906_ = lean_ctor_get(v_arg_4882_, 0);
                    lean_inc(v_n_4906_);
                    lean_dec_ref_known(v_arg_4882_, 1);
                    v___x_4907_ = lean_st_ref_get(v_a_4887_);
                    v_env_4908_ = lean_ctor_get(v___x_4907_, 0);
                    lean_inc_ref(v_env_4908_);
                    lean_dec(v___x_4907_);
                    v___x_4909_ = l_Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs(
                        v_env_4908_,
                        v_n_4906_,
                    );
                    if lean_obj_tag(v___x_4909_) == 1 {
                        v_val_4910_ = lean_ctor_get(v___x_4909_, 0);
                        lean_inc(v_val_4910_);
                        lean_dec_ref_known(v___x_4909_, 1);
                        match lean_obj_tag(v_val_4910_) {
                            0 => {
                                v_cidx_4911_ = lean_ctor_get(v_val_4910_, 0);
                                lean_inc(v_cidx_4911_);
                                v_objArgs_4912_ = lean_ctor_get(v_val_4910_, 1);
                                lean_inc_ref(v_objArgs_4912_);
                                lean_dec_ref_known(v_val_4910_, 4);
                                v___x_4913_ = lean_unsigned_to_nat(1);
                                v___x_4914_ = lean_nat_dec_eq(v_cidx_4911_, v___x_4913_);
                                if v___x_4914_ == 0 {
                                    v___x_4915_ = lean_unsigned_to_nat(2);
                                    v___x_4916_ = lean_nat_dec_eq(v_cidx_4911_, v___x_4915_);
                                    lean_dec(v_cidx_4911_);
                                    if v___x_4916_ == 0 {
                                        lean_dec_ref(v_objArgs_4912_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_4917_ = lean_array_get_size(v_objArgs_4912_);
                                        v___x_4918_ = lean_nat_dec_eq(v___x_4917_, v___x_4915_);
                                        if v___x_4918_ == 0 {
                                            lean_dec_ref(v_objArgs_4912_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_4919_ = lean_array_fget_borrowed(
                                                v_objArgs_4912_,
                                                v___x_4913_,
                                            );
                                            if lean_obj_tag(v___x_4919_) == 0 {
                                                v_val_4920_ = lean_ctor_get(v___x_4919_, 0);
                                                lean_inc(v_val_4920_);
                                                v___x_4921_ = lean_unsigned_to_nat(0);
                                                v___x_4922_ =
                                                    lean_array_fget(v_objArgs_4912_, v___x_4921_);
                                                lean_dec_ref(v_objArgs_4912_);
                                                v___x_4923_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral(v___x_4922_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
                                                if lean_obj_tag(v___x_4923_) == 0 {
                                                    v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
                                                    lean_inc(v_a_4924_);
                                                    if lean_obj_tag(v_a_4924_) == 0 {
                                                        lean_dec(v_val_4920_);
                                                        return v___x_4923_;
                                                    } else {
                                                        v_isSharedCheck_4940_ =
                                                            (!lean_is_exclusive(v___x_4923_)) as u8;
                                                        if v_isSharedCheck_4940_ == 0 {
                                                            v_unused_4941_ =
                                                                lean_ctor_get(v___x_4923_, 0);
                                                            lean_dec(v_unused_4941_);
                                                            v___x_4926_ = v___x_4923_;
                                                            v_isShared_4927_ =
                                                                v_isSharedCheck_4940_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            lean_dec(v___x_4923_);
                                                            v___x_4926_ = lean_box(0);
                                                            v_isShared_4927_ =
                                                                v_isSharedCheck_4940_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec(v_val_4920_);
                                                    return v___x_4923_;
                                                }
                                            } else {
                                                lean_dec_ref(v_objArgs_4912_);
                                                state = 2;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_cidx_4911_);
                                    v___x_4942_ = lean_array_get_size(v_objArgs_4912_);
                                    v___x_4943_ = lean_unsigned_to_nat(2);
                                    v___x_4944_ = lean_nat_dec_eq(v___x_4942_, v___x_4943_);
                                    if v___x_4944_ == 0 {
                                        lean_dec_ref(v_objArgs_4912_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_4945_ = lean_array_fget(v_objArgs_4912_, v___x_4913_);
                                        if lean_obj_tag(v___x_4945_) == 1 {
                                            v___x_4946_ = lean_unsigned_to_nat(0);
                                            v___x_4947_ =
                                                lean_array_fget(v_objArgs_4912_, v___x_4946_);
                                            lean_dec_ref(v_objArgs_4912_);
                                            v___x_4948_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral(v___x_4947_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
                                            if lean_obj_tag(v___x_4948_) == 0 {
                                                v_a_4949_ = lean_ctor_get(v___x_4948_, 0);
                                                lean_inc(v_a_4949_);
                                                if lean_obj_tag(v_a_4949_) == 0 {
                                                    lean_dec_ref_known(v___x_4945_, 1);
                                                    return v___x_4948_;
                                                } else {
                                                    lean_dec_ref_known(v___x_4948_, 1);
                                                    v_val_4950_ = lean_ctor_get(v_a_4949_, 0);
                                                    lean_inc(v_val_4950_);
                                                    lean_dec_ref_known(v_a_4949_, 1);
                                                    v___x_4951_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpStringLiteral___redArg(v___x_4945_, v_a_4887_);
                                                    if lean_obj_tag(v___x_4951_) == 0 {
                                                        v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
                                                        v_isSharedCheck_4972_ =
                                                            (!lean_is_exclusive(v___x_4951_)) as u8;
                                                        if v_isSharedCheck_4972_ == 0 {
                                                            v___x_4954_ = v___x_4951_;
                                                            v_isShared_4955_ =
                                                                v_isSharedCheck_4972_;
                                                            state = 9;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4952_);
                                                            lean_dec(v___x_4951_);
                                                            v___x_4954_ = lean_box(0);
                                                            v_isShared_4955_ =
                                                                v_isSharedCheck_4972_;
                                                            state = 9;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v_val_4950_);
                                                        v_a_4973_ = lean_ctor_get(v___x_4951_, 0);
                                                        v_isSharedCheck_4980_ =
                                                            (!lean_is_exclusive(v___x_4951_)) as u8;
                                                        if v_isSharedCheck_4980_ == 0 {
                                                            v___x_4975_ = v___x_4951_;
                                                            v_isShared_4976_ =
                                                                v_isSharedCheck_4980_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4973_);
                                                            lean_dec(v___x_4951_);
                                                            v___x_4975_ = lean_box(0);
                                                            v_isShared_4976_ =
                                                                v_isSharedCheck_4980_;
                                                            state = 14;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref_known(v___x_4945_, 1);
                                                return v___x_4948_;
                                            }
                                        } else {
                                            lean_dec(v___x_4945_);
                                            lean_dec_ref(v_objArgs_4912_);
                                            state = 2;
                                            continue;
                                        }
                                    }
                                }
                            }
                            3 => {
                                v_args_4981_ = lean_ctor_get(v_val_4910_, 0);
                                v_isSharedCheck_5004_ = (!lean_is_exclusive(v_val_4910_)) as u8;
                                if v_isSharedCheck_5004_ == 0 {
                                    v___x_4983_ = v_val_4910_;
                                    v_isShared_4984_ = v_isSharedCheck_5004_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_args_4981_);
                                    lean_dec(v_val_4910_);
                                    v___x_4983_ = lean_box(0);
                                    v_isShared_4984_ = v_isSharedCheck_5004_;
                                    state = 16;
                                    continue;
                                }
                            }
                            _ => {
                                lean_dec(v_val_4910_);
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4909_);
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_arg_4882_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_4890_ = lean_box(0);
                v___x_4891_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4891_, 0, v___x_4890_);
                return v___x_4891_;
            }
            2 => {
                v___x_4893_ = lean_box(0);
                v___x_4894_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4894_, 0, v___x_4893_);
                return v___x_4894_;
            }
            3 => {
                v___x_4899_ = lean_unsigned_to_nat(0);
                v___x_4900_ = lean_nat_dec_eq(v_val_4895_, v___x_4899_);
                lean_dec(v_val_4895_);
                if v___x_4900_ == 0 {
                    lean_del_object(v___x_4897_);
                    state = 1;
                    continue;
                } else {
                    v___x_4901_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral___closed__0;
                    if v_isShared_4898_ == 0 {
                        lean_ctor_set(v___x_4897_, 0, v___x_4901_);
                        v___x_4903_ = v___x_4897_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4901_);
                        v___x_4903_ = v_reuseFailAlloc_4904_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4903_;
            }
            5 => {
                v_val_4928_ = lean_ctor_get(v_a_4924_, 0);
                v_isSharedCheck_4939_ = (!lean_is_exclusive(v_a_4924_)) as u8;
                if v_isSharedCheck_4939_ == 0 {
                    v___x_4930_ = v_a_4924_;
                    v_isShared_4931_ = v_isSharedCheck_4939_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_val_4928_);
                    lean_dec(v_a_4924_);
                    v___x_4930_ = lean_box(0);
                    v_isShared_4931_ = v_isSharedCheck_4939_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4932_ = l_Lean_Name_num___override(v_val_4928_, v_val_4920_);
                if v_isShared_4931_ == 0 {
                    lean_ctor_set(v___x_4930_, 0, v___x_4932_);
                    v___x_4934_ = v___x_4930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4932_);
                    v___x_4934_ = v_reuseFailAlloc_4938_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4927_ == 0 {
                    lean_ctor_set(v___x_4926_, 0, v___x_4934_);
                    v___x_4936_ = v___x_4926_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4934_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4936_;
            }
            9 => {
                if lean_obj_tag(v_a_4952_) == 0 {
                    lean_dec(v_val_4950_);
                    v___x_4956_ = lean_box(0);
                    if v_isShared_4955_ == 0 {
                        lean_ctor_set(v___x_4954_, 0, v___x_4956_);
                        v___x_4958_ = v___x_4954_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
                        v___x_4958_ = v_reuseFailAlloc_4959_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_val_4960_ = lean_ctor_get(v_a_4952_, 0);
                    v_isSharedCheck_4971_ = (!lean_is_exclusive(v_a_4952_)) as u8;
                    if v_isSharedCheck_4971_ == 0 {
                        v___x_4962_ = v_a_4952_;
                        v_isShared_4963_ = v_isSharedCheck_4971_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_val_4960_);
                        lean_dec(v_a_4952_);
                        v___x_4962_ = lean_box(0);
                        v_isShared_4963_ = v_isSharedCheck_4971_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_4958_;
            }
            11 => {
                v___x_4964_ = l_Lean_Name_str___override(v_val_4950_, v_val_4960_);
                if v_isShared_4963_ == 0 {
                    lean_ctor_set(v___x_4962_, 0, v___x_4964_);
                    v___x_4966_ = v___x_4962_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4970_, 0, v___x_4964_);
                    v___x_4966_ = v_reuseFailAlloc_4970_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4955_ == 0 {
                    lean_ctor_set(v___x_4954_, 0, v___x_4966_);
                    v___x_4968_ = v___x_4954_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4969_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4969_, 0, v___x_4966_);
                    v___x_4968_ = v_reuseFailAlloc_4969_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4968_;
            }
            14 => {
                if v_isShared_4976_ == 0 {
                    v___x_4978_ = v___x_4975_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
                    v___x_4978_ = v_reuseFailAlloc_4979_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4978_;
            }
            16 => {
                v___x_4985_ = lean_box(0);
                v___x_4986_ = lean_unsigned_to_nat(0);
                v___x_4987_ = lean_array_get_size(v_args_4981_);
                v___x_4988_ = lean_nat_dec_lt(v___x_4986_, v___x_4987_);
                if v___x_4988_ == 0 {
                    lean_dec_ref(v_args_4981_);
                    v___x_4989_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral___closed__0;
                    if v_isShared_4984_ == 0 {
                        lean_ctor_set_tag(v___x_4983_, 0);
                        lean_ctor_set(v___x_4983_, 0, v___x_4989_);
                        v___x_4991_ = v___x_4983_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4989_);
                        v___x_4991_ = v_reuseFailAlloc_4992_;
                        state = 17;
                        continue;
                    }
                } else {
                    v___x_4993_ = lean_nat_dec_le(v___x_4987_, v___x_4987_);
                    if v___x_4993_ == 0 {
                        if v___x_4988_ == 0 {
                            lean_dec_ref(v_args_4981_);
                            v___x_4994_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral___closed__0;
                            if v_isShared_4984_ == 0 {
                                lean_ctor_set_tag(v___x_4983_, 0);
                                lean_ctor_set(v___x_4983_, 0, v___x_4994_);
                                v___x_4996_ = v___x_4983_;
                                state = 18;
                                continue;
                            } else {
                                v_reuseFailAlloc_4997_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4997_, 0, v___x_4994_);
                                v___x_4996_ = v_reuseFailAlloc_4997_;
                                state = 18;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4983_);
                            v___x_4998_ = 0usize;
                            v___x_4999_ = lean_usize_of_nat(v___x_4987_);
                            v___x_5000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0___redArg(v_args_4981_, v___x_4998_, v___x_4999_, v___x_4985_, v_a_4887_);
                            lean_dec_ref(v_args_4981_);
                            return v___x_5000_;
                        }
                    } else {
                        lean_del_object(v___x_4983_);
                        v___x_5001_ = 0usize;
                        v___x_5002_ = lean_usize_of_nat(v___x_4987_);
                        v___x_5003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0___redArg(v_args_4981_, v___x_5001_, v___x_5002_, v___x_4985_, v_a_4887_);
                        lean_dec_ref(v_args_4981_);
                        return v___x_5003_;
                    }
                }
            }
            17 => {
                return v___x_4991_;
            }
            18 => {
                return v___x_4996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral___boxed(
    mut v_arg_5005_: *mut LeanObject,
    mut v_a_5006_: *mut LeanObject,
    mut v_a_5007_: *mut LeanObject,
    mut v_a_5008_: *mut LeanObject,
    mut v_a_5009_: *mut LeanObject,
    mut v_a_5010_: *mut LeanObject,
    mut v_a_5011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5012_: *mut LeanObject = core::ptr::null_mut();
    v_res_5012_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral(v_arg_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_);
    lean_dec(v_a_5010_);
    lean_dec_ref(v_a_5009_);
    lean_dec(v_a_5008_);
    lean_dec_ref(v_a_5007_);
    lean_dec(v_a_5006_);
    return v_res_5012_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0(
    mut v_as_5013_: *mut LeanObject,
    mut v_i_5014_: usize,
    mut v_stop_5015_: usize,
    mut v_b_5016_: *mut LeanObject,
    mut v___y_5017_: *mut LeanObject,
    mut v___y_5018_: *mut LeanObject,
    mut v___y_5019_: *mut LeanObject,
    mut v___y_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    v___x_5023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0___redArg(v_as_5013_, v_i_5014_, v_stop_5015_, v_b_5016_, v___y_5021_);
    return v___x_5023_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0___boxed(
    mut v_as_5024_: *mut LeanObject,
    mut v_i_5025_: *mut LeanObject,
    mut v_stop_5026_: *mut LeanObject,
    mut v_b_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
    mut v___y_5033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5034_: usize = 0;
    let mut v_stop_boxed_5035_: usize = 0;
    let mut v_res_5036_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5034_ = lean_unbox_usize(v_i_5025_);
    lean_dec(v_i_5025_);
    v_stop_boxed_5035_ = lean_unbox_usize(v_stop_5026_);
    lean_dec(v_stop_5026_);
    v_res_5036_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral_spec__0(v_as_5024_, v_i_boxed_5034_, v_stop_boxed_5035_, v_b_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
    lean_dec(v___y_5032_);
    lean_dec_ref(v___y_5031_);
    lean_dec(v___y_5030_);
    lean_dec_ref(v___y_5029_);
    lean_dec(v___y_5028_);
    lean_dec_ref(v_as_5024_);
    return v_res_5036_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0___redArg(
    mut v_as_5037_: *mut LeanObject,
    mut v_sz_5038_: usize,
    mut v_i_5039_: usize,
    mut v_b_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5044_: u8 = 0;
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5062_: u8 = 0;
    let mut v_fst_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5067_: u8 = 0;
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5070_: u64 = 0;
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: usize = 0;
    let mut v___x_5078_: usize = 0;
    let mut v_reuseFailAlloc_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: u64 = 0;
    let mut v_hash_5083_: u64 = 0;
    let mut v_isSharedCheck_5084_: u8 = 0;
    let mut v_isSharedCheck_5085_: u8 = 0;
    let mut v_isSharedCheck_5086_: u8 = 0;
    let mut v_a_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5094_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5044_ = lean_usize_dec_lt(v_i_5039_, v_sz_5038_);
                if v___x_5044_ == 0 {
                    v___x_5045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5045_, 0, v_b_5040_);
                    v___x_5046_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5046_, 0, v___x_5045_);
                    return v___x_5046_;
                } else {
                    v_a_5047_ = lean_array_uget_borrowed(v_as_5037_, v_i_5039_);
                    lean_inc(v_a_5047_);
                    v___x_5048_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg___redArg(v_a_5047_, v___y_5041_, v___y_5042_);
                    if lean_obj_tag(v___x_5048_) == 0 {
                        v_a_5049_ = lean_ctor_get(v___x_5048_, 0);
                        v_isSharedCheck_5086_ = (!lean_is_exclusive(v___x_5048_)) as u8;
                        if v_isSharedCheck_5086_ == 0 {
                            v___x_5051_ = v___x_5048_;
                            v_isShared_5052_ = v_isSharedCheck_5086_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5049_);
                            lean_dec(v___x_5048_);
                            v___x_5051_ = lean_box(0);
                            v_isShared_5052_ = v_isSharedCheck_5086_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_5040_);
                        v_a_5087_ = lean_ctor_get(v___x_5048_, 0);
                        v_isSharedCheck_5094_ = (!lean_is_exclusive(v___x_5048_)) as u8;
                        if v_isSharedCheck_5094_ == 0 {
                            v___x_5089_ = v___x_5048_;
                            v_isShared_5090_ = v_isSharedCheck_5094_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5087_);
                            lean_dec(v___x_5048_);
                            v___x_5089_ = lean_box(0);
                            v_isShared_5090_ = v_isSharedCheck_5094_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5049_) == 0 {
                    lean_dec_ref(v_b_5040_);
                    v___x_5053_ = lean_box(0);
                    if v_isShared_5052_ == 0 {
                        lean_ctor_set(v___x_5051_, 0, v___x_5053_);
                        v___x_5055_ = v___x_5051_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5053_);
                        v___x_5055_ = v_reuseFailAlloc_5056_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5051_);
                    v_val_5057_ = lean_ctor_get(v_a_5049_, 0);
                    lean_inc(v_val_5057_);
                    lean_dec_ref_known(v_a_5049_, 1);
                    v_fst_5058_ = lean_ctor_get(v_val_5057_, 0);
                    v_snd_5059_ = lean_ctor_get(v_val_5057_, 1);
                    v_isSharedCheck_5085_ = (!lean_is_exclusive(v_val_5057_)) as u8;
                    if v_isSharedCheck_5085_ == 0 {
                        v___x_5061_ = v_val_5057_;
                        v_isShared_5062_ = v_isSharedCheck_5085_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_5059_);
                        lean_inc(v_fst_5058_);
                        lean_dec(v_val_5057_);
                        v___x_5061_ = lean_box(0);
                        v_isShared_5062_ = v_isSharedCheck_5085_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5055_;
            }
            3 => {
                v_fst_5063_ = lean_ctor_get(v_b_5040_, 0);
                v_snd_5064_ = lean_ctor_get(v_b_5040_, 1);
                v_isSharedCheck_5084_ = (!lean_is_exclusive(v_b_5040_)) as u8;
                if v_isSharedCheck_5084_ == 0 {
                    v___x_5066_ = v_b_5040_;
                    v_isShared_5067_ = v_isSharedCheck_5084_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_5064_);
                    lean_inc(v_fst_5063_);
                    lean_dec(v_b_5040_);
                    v___x_5066_ = lean_box(0);
                    v_isShared_5067_ = v_isSharedCheck_5084_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5068_ = l_Lean_Name_str___override(v_fst_5063_, v_snd_5059_);
                if lean_obj_tag(v___x_5068_) == 0 {
                    v___x_5082_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0);
                    v___y_5070_ = v___x_5082_;
                    state = 5;
                    continue;
                } else {
                    v_hash_5083_ = lean_ctor_get_uint64(
                        v___x_5068_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_5070_ = v_hash_5083_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5071_ = lean_box_uint64(v___y_5070_);
                if v_isShared_5067_ == 0 {
                    lean_ctor_set(v___x_5066_, 1, v___x_5071_);
                    lean_ctor_set(v___x_5066_, 0, v_fst_5058_);
                    v___x_5073_ = v___x_5066_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_fst_5058_);
                    lean_ctor_set(v_reuseFailAlloc_5081_, 1, v___x_5071_);
                    v___x_5073_ = v_reuseFailAlloc_5081_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5074_ = lean_array_push(v_snd_5064_, v___x_5073_);
                if v_isShared_5062_ == 0 {
                    lean_ctor_set(v___x_5061_, 1, v___x_5074_);
                    lean_ctor_set(v___x_5061_, 0, v___x_5068_);
                    v___x_5076_ = v___x_5061_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5080_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_5068_);
                    lean_ctor_set(v_reuseFailAlloc_5080_, 1, v___x_5074_);
                    v___x_5076_ = v_reuseFailAlloc_5080_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5077_ = 1usize;
                v___x_5078_ = lean_usize_add(v_i_5039_, v___x_5077_);
                v_i_5039_ = v___x_5078_;
                v_b_5040_ = v___x_5076_;
                state = 0;
                continue;
            }
            8 => {
                if v_isShared_5090_ == 0 {
                    v___x_5092_ = v___x_5089_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
                    v___x_5092_ = v_reuseFailAlloc_5093_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0___redArg___boxed(
    mut v_as_5095_: *mut LeanObject,
    mut v_sz_5096_: *mut LeanObject,
    mut v_i_5097_: *mut LeanObject,
    mut v_b_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5102_: usize = 0;
    let mut v_i_boxed_5103_: usize = 0;
    let mut v_res_5104_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5102_ = lean_unbox_usize(v_sz_5096_);
    lean_dec(v_sz_5096_);
    v_i_boxed_5103_ = lean_unbox_usize(v_i_5097_);
    lean_dec(v_i_5097_);
    v_res_5104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0___redArg(v_as_5095_, v_sz_boxed_5102_, v_i_boxed_5103_, v_b_5098_, v___y_5099_, v___y_5100_);
    lean_dec(v___y_5100_);
    lean_dec(v___y_5099_);
    lean_dec_ref(v_as_5095_);
    return v_res_5104_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1___redArg(
    mut v_x_5105_: *mut LeanObject,
    mut v_x_5106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v_val_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u8 = 0;
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut v_unused_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5105_) == 0 {
                    v___x_5108_ = l_List_reverse___redArg(v_x_5106_);
                    v___x_5109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5109_, 0, v___x_5108_);
                    v___x_5110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5110_, 0, v___x_5109_);
                    return v___x_5110_;
                } else {
                    v_head_5111_ = lean_ctor_get(v_x_5105_, 0);
                    lean_inc(v_head_5111_);
                    if lean_obj_tag(v_head_5111_) == 0 {
                        v_tail_5112_ = lean_ctor_get(v_x_5105_, 1);
                        v_isSharedCheck_5123_ = (!lean_is_exclusive(v_x_5105_)) as u8;
                        if v_isSharedCheck_5123_ == 0 {
                            v_unused_5124_ = lean_ctor_get(v_x_5105_, 0);
                            lean_dec(v_unused_5124_);
                            v___x_5114_ = v_x_5105_;
                            v_isShared_5115_ = v_isSharedCheck_5123_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_5112_);
                            lean_dec(v_x_5105_);
                            v___x_5114_ = lean_box(0);
                            v_isShared_5115_ = v_isSharedCheck_5123_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_5105_, 2);
                        lean_dec(v_head_5111_);
                        lean_dec(v_x_5106_);
                        v___x_5125_ = lean_box(0);
                        v___x_5126_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5126_, 0, v___x_5125_);
                        return v___x_5126_;
                    }
                }
            }
            1 => {
                v_val_5116_ = lean_ctor_get(v_head_5111_, 0);
                lean_inc(v_val_5116_);
                lean_dec_ref_known(v_head_5111_, 1);
                v___x_5117_ = lean_uint8_of_nat(v_val_5116_);
                lean_dec(v_val_5116_);
                v___x_5118_ = lean_box((v___x_5117_) as usize);
                if v_isShared_5115_ == 0 {
                    lean_ctor_set(v___x_5114_, 1, v_x_5106_);
                    lean_ctor_set(v___x_5114_, 0, v___x_5118_);
                    v___x_5120_ = v___x_5114_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5118_);
                    lean_ctor_set(v_reuseFailAlloc_5122_, 1, v_x_5106_);
                    v___x_5120_ = v_reuseFailAlloc_5122_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_x_5105_ = v_tail_5112_;
                v_x_5106_ = v___x_5120_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1___redArg___boxed(
    mut v_x_5127_: *mut LeanObject,
    mut v_x_5128_: *mut LeanObject,
    mut v___y_5129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5130_: *mut LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1___redArg(v_x_5127_, v_x_5128_);
    return v_res_5130_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2___redArg(
    mut v_sz_5131_: usize,
    mut v_i_5132_: usize,
    mut v_bs_5133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5135_: u8 = 0;
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: u8 = 0;
    let mut v___x_5143_: usize = 0;
    let mut v___x_5144_: usize = 0;
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5135_ = lean_usize_dec_lt(v_i_5132_, v_sz_5131_);
                if v___x_5135_ == 0 {
                    v___x_5136_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5136_, 0, v_bs_5133_);
                    v___x_5137_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5137_, 0, v___x_5136_);
                    return v___x_5137_;
                } else {
                    v_v_5138_ = lean_array_uget_borrowed(v_bs_5133_, v_i_5132_);
                    if lean_obj_tag(v_v_5138_) == 0 {
                        v_val_5139_ = lean_ctor_get(v_v_5138_, 0);
                        lean_inc(v_val_5139_);
                        v___x_5140_ = lean_unsigned_to_nat(0);
                        v_bs_x27_5141_ = lean_array_uset(v_bs_5133_, v_i_5132_, v___x_5140_);
                        v___x_5142_ = lean_uint8_of_nat(v_val_5139_);
                        lean_dec(v_val_5139_);
                        v___x_5143_ = 1usize;
                        v___x_5144_ = lean_usize_add(v_i_5132_, v___x_5143_);
                        v___x_5145_ = lean_box((v___x_5142_) as usize);
                        v___x_5146_ = lean_array_uset(v_bs_x27_5141_, v_i_5132_, v___x_5145_);
                        v_i_5132_ = v___x_5144_;
                        v_bs_5133_ = v___x_5146_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_5133_);
                        v___x_5148_ = lean_box(0);
                        v___x_5149_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5149_, 0, v___x_5148_);
                        return v___x_5149_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2___redArg___boxed(
    mut v_sz_5150_: *mut LeanObject,
    mut v_i_5151_: *mut LeanObject,
    mut v_bs_5152_: *mut LeanObject,
    mut v___y_5153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5154_: usize = 0;
    let mut v_i_boxed_5155_: usize = 0;
    let mut v_res_5156_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5154_ = lean_unbox_usize(v_sz_5150_);
    lean_dec(v_sz_5150_);
    v_i_boxed_5155_ = lean_unbox_usize(v_i_5151_);
    lean_dec(v_i_5151_);
    v_res_5156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2___redArg(v_sz_boxed_5154_, v_i_boxed_5155_, v_bs_5152_);
    return v_res_5156_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet(
    mut v_e_5184_: *mut LeanObject,
    mut v_a_5185_: *mut LeanObject,
    mut v_a_5186_: *mut LeanObject,
    mut v_a_5187_: *mut LeanObject,
    mut v_a_5188_: *mut LeanObject,
    mut v_a_5189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nameAcc_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_processedArgs_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5205_: usize = 0;
    let mut v___x_5206_: usize = 0;
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5219_: u8 = 0;
    let mut v_snd_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5228_: u8 = 0;
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut v_a_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5233_: u8 = 0;
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5237_: u8 = 0;
    let mut v_c_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: u8 = 0;
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sizeId_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5267_: u8 = 0;
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u8 = 0;
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut v_value_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5278_: u8 = 0;
    let mut v_val_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5282_: u8 = 0;
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5290_: u8 = 0;
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5295_: u8 = 0;
    let mut v_i_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5302_: u8 = 0;
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: u8 = 0;
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5310_: u8 = 0;
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5327_: u8 = 0;
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_a_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut v___x_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: u8 = 0;
    let mut v_fn_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: u8 = 0;
    let mut v___x_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: u8 = 0;
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: u8 = 0;
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: u8 = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: u8 = 0;
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: u8 = 0;
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: u8 = 0;
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5399_: u8 = 0;
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5406_: u8 = 0;
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5414_: u8 = 0;
    let mut v_fst_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5421_: u8 = 0;
    let mut v___y_5423_: u64 = 0;
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: u64 = 0;
    let mut v_hash_5447_: u64 = 0;
    let mut v_isSharedCheck_5448_: u8 = 0;
    let mut v_a_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5452_: u8 = 0;
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5456_: u8 = 0;
    let mut v_isSharedCheck_5457_: u8 = 0;
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v_isSharedCheck_5460_: u8 = 0;
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: u8 = 0;
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: u8 = 0;
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5477_: u8 = 0;
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5489_: u8 = 0;
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5497_: u8 = 0;
    let mut v_val_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5503_: u8 = 0;
    let mut v___y_5505_: u64 = 0;
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: u64 = 0;
    let mut v_hash_5526_: u64 = 0;
    let mut v_isSharedCheck_5527_: u8 = 0;
    let mut v_a_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5531_: u8 = 0;
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5535_: u8 = 0;
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5540_: u8 = 0;
    let mut v_isSharedCheck_5541_: u8 = 0;
    let mut v_isSharedCheck_5542_: u8 = 0;
    let mut v_args_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: u8 = 0;
    let mut v_args_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: u8 = 0;
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: u8 = 0;
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: u8 = 0;
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: u8 = 0;
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: u8 = 0;
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: u8 = 0;
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: u8 = 0;
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: u8 = 0;
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: u8 = 0;
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: u8 = 0;
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: u8 = 0;
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: u8 = 0;
    let mut v_args_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: u8 = 0;
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: u8 = 0;
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: u8 = 0;
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: u8 = 0;
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: u8 = 0;
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5619_: u8 = 0;
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elems_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remainingCapacity_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5635_: u8 = 0;
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5643_: u8 = 0;
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5653_: u8 = 0;
    let mut v_isSharedCheck_5654_: u8 = 0;
    let mut v_arg_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elems_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5664_: u8 = 0;
    let mut v_sz_5665_: usize = 0;
    let mut v___x_5666_: usize = 0;
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5679_: u8 = 0;
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5689_: u8 = 0;
    let mut v_isSharedCheck_5690_: u8 = 0;
    let mut v_a_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5694_: u8 = 0;
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5698_: u8 = 0;
    let mut v_isSharedCheck_5699_: u8 = 0;
    let mut v_isSharedCheck_5700_: u8 = 0;
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: u8 = 0;
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: u8 = 0;
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: u8 = 0;
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: u8 = 0;
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elems_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remainingCapacity_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5739_: u8 = 0;
    let mut v___x_5740_: u8 = 0;
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5746_: u8 = 0;
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5761_: u8 = 0;
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5770_: u8 = 0;
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5775_: u8 = 0;
    let mut v_isSharedCheck_5776_: u8 = 0;
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: u8 = 0;
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: u8 = 0;
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: u8 = 0;
    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: u8 = 0;
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: u8 = 0;
    let mut v_args_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: u8 = 0;
    let mut v_args_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: u8 = 0;
    let mut v_fvarId_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5818_: u64 = 0;
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5825_: u64 = 0;
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5845_: u8 = 0;
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5850_: u8 = 0;
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5858_: u8 = 0;
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5868_: u8 = 0;
    let mut v_isSharedCheck_5869_: u8 = 0;
    let mut v_a_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5873_: u8 = 0;
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5877_: u8 = 0;
    let mut v_isSharedCheck_5878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_5184_) {
                0 => {
                    v_value_5275_ = lean_ctor_get(v_e_5184_, 0);
                    v_isSharedCheck_5295_ = (!lean_is_exclusive(v_e_5184_)) as u8;
                    if v_isSharedCheck_5295_ == 0 {
                        v___x_5277_ = v_e_5184_;
                        v_isShared_5278_ = v_isSharedCheck_5295_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_value_5275_);
                        lean_dec(v_e_5184_);
                        v___x_5277_ = lean_box(0);
                        v_isShared_5278_ = v_isSharedCheck_5295_;
                        state = 17;
                        continue;
                    }
                }
                5 => {
                    v_i_5296_ = lean_ctor_get(v_e_5184_, 0);
                    lean_inc_ref(v_i_5296_);
                    v_args_5297_ = lean_ctor_get(v_e_5184_, 1);
                    lean_inc_ref(v_args_5297_);
                    lean_dec_ref_known(v_e_5184_, 2);
                    v_cidx_5298_ = lean_ctor_get(v_i_5296_, 1);
                    lean_inc(v_cidx_5298_);
                    v_usize_5299_ = lean_ctor_get(v_i_5296_, 3);
                    lean_inc(v_usize_5299_);
                    v_ssize_5300_ = lean_ctor_get(v_i_5296_, 4);
                    lean_inc(v_ssize_5300_);
                    lean_dec_ref(v_i_5296_);
                    v___x_5337_ = lean_unsigned_to_nat(0);
                    v___x_5338_ = lean_nat_dec_eq(v_usize_5299_, v___x_5337_);
                    lean_dec(v_usize_5299_);
                    if v___x_5338_ == 0 {
                        lean_dec(v_ssize_5300_);
                        v___y_5302_ = v___x_5338_;
                        state = 22;
                        continue;
                    } else {
                        v___x_5339_ = lean_nat_dec_eq(v_ssize_5300_, v___x_5337_);
                        lean_dec(v_ssize_5300_);
                        v___y_5302_ = v___x_5339_;
                        state = 22;
                        continue;
                    }
                }
                9 => {
                    v_fn_5340_ = lean_ctor_get(v_e_5184_, 0);
                    lean_inc(v_fn_5340_);
                    if lean_obj_tag(v_fn_5340_) == 1 {
                        v_pre_5341_ = lean_ctor_get(v_fn_5340_, 0);
                        if lean_obj_tag(v_pre_5341_) == 1 {
                            v_pre_5342_ = lean_ctor_get(v_pre_5341_, 0);
                            match lean_obj_tag(v_pre_5342_) {
                                1 => {
                                    v_pre_5343_ = lean_ctor_get(v_pre_5342_, 0);
                                    match lean_obj_tag(v_pre_5343_) {
                                        1 => {
                                            v_pre_5344_ = lean_ctor_get(v_pre_5343_, 0);
                                            if lean_obj_tag(v_pre_5344_) == 0 {
                                                v_args_5345_ = lean_ctor_get(v_e_5184_, 1);
                                                lean_inc_ref(v_args_5345_);
                                                lean_dec_ref_known(v_e_5184_, 2);
                                                v_str_5346_ = lean_ctor_get(v_fn_5340_, 1);
                                                v_str_5347_ = lean_ctor_get(v_pre_5341_, 1);
                                                v_str_5348_ = lean_ctor_get(v_pre_5342_, 1);
                                                v_str_5349_ = lean_ctor_get(v_pre_5343_, 1);
                                                v___x_5350_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4;
                                                v___x_5351_ =
                                                    lean_string_dec_eq(v_str_5349_, v___x_5350_);
                                                if v___x_5351_ == 0 {
                                                    v___x_5352_ = lean_array_get_size(v_args_5345_);
                                                    lean_dec_ref(v_args_5345_);
                                                    v___x_5353_ = lean_unsigned_to_nat(0);
                                                    v___x_5354_ =
                                                        lean_nat_dec_eq(v___x_5352_, v___x_5353_);
                                                    if v___x_5354_ == 0 {
                                                        lean_dec_ref_known(v_fn_5340_, 2);
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        v_c_5239_ = v_fn_5340_;
                                                        v___y_5240_ = v_a_5189_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_inc_ref(v_str_5348_);
                                                    lean_inc_ref(v_str_5347_);
                                                    lean_inc_ref(v_str_5346_);
                                                    lean_inc(v_pre_5344_);
                                                    lean_dec_ref_known(v_fn_5340_, 2);
                                                    v___x_5355_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__5;
                                                    v___x_5356_ = lean_string_dec_eq(
                                                        v_str_5348_,
                                                        v___x_5355_,
                                                    );
                                                    if v___x_5356_ == 0 {
                                                        v___x_5357_ =
                                                            lean_array_get_size(v_args_5345_);
                                                        lean_dec_ref(v_args_5345_);
                                                        v___x_5358_ = lean_unsigned_to_nat(0);
                                                        v___x_5359_ = lean_nat_dec_eq(
                                                            v___x_5357_,
                                                            v___x_5358_,
                                                        );
                                                        if v___x_5359_ == 0 {
                                                            lean_dec_ref(v_str_5348_);
                                                            lean_dec_ref(v_str_5347_);
                                                            lean_dec_ref(v_str_5346_);
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            v___x_5360_ =
                                                                l_Lean_Name_str___override(
                                                                    v_pre_5344_,
                                                                    v___x_5350_,
                                                                );
                                                            v___x_5361_ =
                                                                l_Lean_Name_str___override(
                                                                    v___x_5360_,
                                                                    v_str_5348_,
                                                                );
                                                            v___x_5362_ =
                                                                l_Lean_Name_str___override(
                                                                    v___x_5361_,
                                                                    v_str_5347_,
                                                                );
                                                            v___x_5363_ =
                                                                l_Lean_Name_str___override(
                                                                    v___x_5362_,
                                                                    v_str_5346_,
                                                                );
                                                            v_c_5239_ = v___x_5363_;
                                                            v___y_5240_ = v_a_5189_;
                                                            state = 10;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_str_5348_);
                                                        v___x_5364_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__6;
                                                        v___x_5365_ = lean_string_dec_eq(
                                                            v_str_5347_,
                                                            v___x_5364_,
                                                        );
                                                        if v___x_5365_ == 0 {
                                                            v___x_5366_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__7;
                                                            v___x_5367_ = lean_string_dec_eq(
                                                                v_str_5347_,
                                                                v___x_5366_,
                                                            );
                                                            if v___x_5367_ == 0 {
                                                                v___x_5368_ = lean_array_get_size(
                                                                    v_args_5345_,
                                                                );
                                                                lean_dec_ref(v_args_5345_);
                                                                v___x_5369_ =
                                                                    lean_unsigned_to_nat(0);
                                                                v___x_5370_ = lean_nat_dec_eq(
                                                                    v___x_5368_,
                                                                    v___x_5369_,
                                                                );
                                                                if v___x_5370_ == 0 {
                                                                    lean_dec_ref(v_str_5347_);
                                                                    lean_dec_ref(v_str_5346_);
                                                                    state = 11;
                                                                    continue;
                                                                } else {
                                                                    v___x_5371_ =
                                                                        l_Lean_Name_str___override(
                                                                            v_pre_5344_,
                                                                            v___x_5350_,
                                                                        );
                                                                    v___x_5372_ =
                                                                        l_Lean_Name_str___override(
                                                                            v___x_5371_,
                                                                            v___x_5355_,
                                                                        );
                                                                    v___x_5373_ =
                                                                        l_Lean_Name_str___override(
                                                                            v___x_5372_,
                                                                            v_str_5347_,
                                                                        );
                                                                    v___x_5374_ =
                                                                        l_Lean_Name_str___override(
                                                                            v___x_5373_,
                                                                            v_str_5346_,
                                                                        );
                                                                    v_c_5239_ = v___x_5374_;
                                                                    v___y_5240_ = v_a_5189_;
                                                                    state = 10;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_str_5347_);
                                                                v___x_5375_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__8;
                                                                v___x_5376_ = lean_string_dec_eq(
                                                                    v_str_5346_,
                                                                    v___x_5375_,
                                                                );
                                                                if v___x_5376_ == 0 {
                                                                    v___x_5377_ =
                                                                        lean_array_get_size(
                                                                            v_args_5345_,
                                                                        );
                                                                    lean_dec_ref(v_args_5345_);
                                                                    v___x_5378_ =
                                                                        lean_unsigned_to_nat(0);
                                                                    v___x_5379_ = lean_nat_dec_eq(
                                                                        v___x_5377_,
                                                                        v___x_5378_,
                                                                    );
                                                                    if v___x_5379_ == 0 {
                                                                        lean_dec_ref(v_str_5346_);
                                                                        state = 11;
                                                                        continue;
                                                                    } else {
                                                                        v___x_5380_ = l_Lean_Name_str___override(v_pre_5344_, v___x_5350_);
                                                                        v___x_5381_ = l_Lean_Name_str___override(v___x_5380_, v___x_5355_);
                                                                        v___x_5382_ = l_Lean_Name_str___override(v___x_5381_, v___x_5366_);
                                                                        v___x_5383_ = l_Lean_Name_str___override(v___x_5382_, v_str_5346_);
                                                                        v_c_5239_ = v___x_5383_;
                                                                        v___y_5240_ = v_a_5189_;
                                                                        state = 10;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_str_5346_);
                                                                    v___x_5384_ = lean_box(0);
                                                                    v___x_5385_ =
                                                                        lean_unsigned_to_nat(0);
                                                                    v___x_5386_ =
                                                                        lean_array_get_borrowed(
                                                                            v___x_5384_,
                                                                            v_args_5345_,
                                                                            v___x_5385_,
                                                                        );
                                                                    lean_inc(v___x_5386_);
                                                                    v___x_5387_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg(v___x_5386_, v_a_5185_);
                                                                    v_a_5388_ = lean_ctor_get(
                                                                        v___x_5387_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_5460_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_5387_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_5460_ == 0 {
                                                                        v___x_5390_ = v___x_5387_;
                                                                        v_isShared_5391_ =
                                                                            v_isSharedCheck_5460_;
                                                                        state = 30;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_5388_);
                                                                        lean_dec(v___x_5387_);
                                                                        v___x_5390_ = lean_box(0);
                                                                        v_isShared_5391_ =
                                                                            v_isSharedCheck_5460_;
                                                                        state = 30;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_str_5347_);
                                                            v___x_5461_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__8;
                                                            v___x_5462_ = lean_string_dec_eq(
                                                                v_str_5346_,
                                                                v___x_5461_,
                                                            );
                                                            if v___x_5462_ == 0 {
                                                                v___x_5463_ = lean_array_get_size(
                                                                    v_args_5345_,
                                                                );
                                                                lean_dec_ref(v_args_5345_);
                                                                v___x_5464_ =
                                                                    lean_unsigned_to_nat(0);
                                                                v___x_5465_ = lean_nat_dec_eq(
                                                                    v___x_5463_,
                                                                    v___x_5464_,
                                                                );
                                                                if v___x_5465_ == 0 {
                                                                    lean_dec_ref(v_str_5346_);
                                                                    state = 11;
                                                                    continue;
                                                                } else {
                                                                    v___x_5466_ =
                                                                        l_Lean_Name_str___override(
                                                                            v_pre_5344_,
                                                                            v___x_5350_,
                                                                        );
                                                                    v___x_5467_ =
                                                                        l_Lean_Name_str___override(
                                                                            v___x_5466_,
                                                                            v___x_5355_,
                                                                        );
                                                                    v___x_5468_ =
                                                                        l_Lean_Name_str___override(
                                                                            v___x_5467_,
                                                                            v___x_5364_,
                                                                        );
                                                                    v___x_5469_ =
                                                                        l_Lean_Name_str___override(
                                                                            v___x_5468_,
                                                                            v_str_5346_,
                                                                        );
                                                                    v_c_5239_ = v___x_5469_;
                                                                    v___y_5240_ = v_a_5189_;
                                                                    state = 10;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_str_5346_);
                                                                v___x_5470_ = lean_box(0);
                                                                v___x_5471_ =
                                                                    lean_unsigned_to_nat(0);
                                                                v___x_5472_ =
                                                                    lean_array_get_borrowed(
                                                                        v___x_5470_,
                                                                        v_args_5345_,
                                                                        v___x_5471_,
                                                                    );
                                                                lean_inc(v___x_5472_);
                                                                v___x_5473_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg(v___x_5472_, v_a_5185_);
                                                                v_a_5474_ =
                                                                    lean_ctor_get(v___x_5473_, 0);
                                                                v_isSharedCheck_5542_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_5473_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_5542_ == 0 {
                                                                    v___x_5476_ = v___x_5473_;
                                                                    v_isShared_5477_ =
                                                                        v_isSharedCheck_5542_;
                                                                    state = 44;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_5474_);
                                                                    lean_dec(v___x_5473_);
                                                                    v___x_5476_ = lean_box(0);
                                                                    v_isShared_5477_ =
                                                                        v_isSharedCheck_5542_;
                                                                    state = 44;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                v_args_5543_ = lean_ctor_get(v_e_5184_, 1);
                                                lean_inc_ref(v_args_5543_);
                                                lean_dec_ref_known(v_e_5184_, 2);
                                                v___x_5544_ = lean_array_get_size(v_args_5543_);
                                                lean_dec_ref(v_args_5543_);
                                                v___x_5545_ = lean_unsigned_to_nat(0);
                                                v___x_5546_ =
                                                    lean_nat_dec_eq(v___x_5544_, v___x_5545_);
                                                if v___x_5546_ == 0 {
                                                    lean_dec_ref_known(v_fn_5340_, 2);
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    v_c_5239_ = v_fn_5340_;
                                                    v___y_5240_ = v_a_5189_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        }
                                        0 => {
                                            v_args_5547_ = lean_ctor_get(v_e_5184_, 1);
                                            lean_inc_ref(v_args_5547_);
                                            lean_dec_ref_known(v_e_5184_, 2);
                                            v_str_5548_ = lean_ctor_get(v_fn_5340_, 1);
                                            v_str_5549_ = lean_ctor_get(v_pre_5341_, 1);
                                            v_str_5550_ = lean_ctor_get(v_pre_5342_, 1);
                                            v___x_5551_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__4;
                                            v___x_5552_ =
                                                lean_string_dec_eq(v_str_5550_, v___x_5551_);
                                            if v___x_5552_ == 0 {
                                                v___x_5553_ = lean_array_get_size(v_args_5547_);
                                                lean_dec_ref(v_args_5547_);
                                                v___x_5554_ = lean_unsigned_to_nat(0);
                                                v___x_5555_ =
                                                    lean_nat_dec_eq(v___x_5553_, v___x_5554_);
                                                if v___x_5555_ == 0 {
                                                    lean_dec_ref_known(v_fn_5340_, 2);
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    v_c_5239_ = v_fn_5340_;
                                                    v___y_5240_ = v_a_5189_;
                                                    state = 10;
                                                    continue;
                                                }
                                            } else {
                                                lean_inc_ref(v_str_5549_);
                                                lean_inc_ref(v_str_5548_);
                                                lean_inc(v_pre_5343_);
                                                lean_dec_ref_known(v_fn_5340_, 2);
                                                v___x_5556_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__5;
                                                v___x_5557_ =
                                                    lean_string_dec_eq(v_str_5549_, v___x_5556_);
                                                if v___x_5557_ == 0 {
                                                    v___x_5558_ = lean_array_get_size(v_args_5547_);
                                                    lean_dec_ref(v_args_5547_);
                                                    v___x_5559_ = lean_unsigned_to_nat(0);
                                                    v___x_5560_ =
                                                        lean_nat_dec_eq(v___x_5558_, v___x_5559_);
                                                    if v___x_5560_ == 0 {
                                                        lean_dec_ref(v_str_5549_);
                                                        lean_dec_ref(v_str_5548_);
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        v___x_5561_ = l_Lean_Name_str___override(
                                                            v_pre_5343_,
                                                            v___x_5551_,
                                                        );
                                                        v___x_5562_ = l_Lean_Name_str___override(
                                                            v___x_5561_,
                                                            v_str_5549_,
                                                        );
                                                        v___x_5563_ = l_Lean_Name_str___override(
                                                            v___x_5562_,
                                                            v_str_5548_,
                                                        );
                                                        v_c_5239_ = v___x_5563_;
                                                        v___y_5240_ = v_a_5189_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_str_5549_);
                                                    v___x_5564_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__9;
                                                    v___x_5565_ = lean_string_dec_eq(
                                                        v_str_5548_,
                                                        v___x_5564_,
                                                    );
                                                    if v___x_5565_ == 0 {
                                                        v___x_5566_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__10;
                                                        v___x_5567_ = lean_string_dec_eq(
                                                            v_str_5548_,
                                                            v___x_5566_,
                                                        );
                                                        if v___x_5567_ == 0 {
                                                            v___x_5568_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__11;
                                                            v___x_5569_ = lean_string_dec_eq(
                                                                v_str_5548_,
                                                                v___x_5568_,
                                                            );
                                                            if v___x_5569_ == 0 {
                                                                v___x_5570_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__12;
                                                                v___x_5571_ = lean_string_dec_eq(
                                                                    v_str_5548_,
                                                                    v___x_5570_,
                                                                );
                                                                if v___x_5571_ == 0 {
                                                                    v___x_5572_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__13;
                                                                    v___x_5573_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_5548_,
                                                                            v___x_5572_,
                                                                        );
                                                                    if v___x_5573_ == 0 {
                                                                        v___x_5574_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__14;
                                                                        v___x_5575_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_5548_,
                                                                                v___x_5574_,
                                                                            );
                                                                        if v___x_5575_ == 0 {
                                                                            v___x_5576_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__15;
                                                                            v___x_5577_ =
                                                                                lean_string_dec_eq(
                                                                                    v_str_5548_,
                                                                                    v___x_5576_,
                                                                                );
                                                                            if v___x_5577_ == 0 {
                                                                                v___x_5578_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__16;
                                                                                v___x_5579_ = lean_string_dec_eq(v_str_5548_, v___x_5578_);
                                                                                if v___x_5579_ == 0
                                                                                {
                                                                                    v___x_5580_ = lean_array_get_size(v_args_5547_);
                                                                                    lean_dec_ref(v_args_5547_);
                                                                                    v___x_5581_ = lean_unsigned_to_nat(0);
                                                                                    v___x_5582_ = lean_nat_dec_eq(v___x_5580_, v___x_5581_);
                                                                                    if v___x_5582_
                                                                                        == 0
                                                                                    {
                                                                                        lean_dec_ref(v_str_5548_);
                                                                                        state = 11;
                                                                                        continue;
                                                                                    } else {
                                                                                        v___x_5583_ = l_Lean_Name_str___override(v_pre_5343_, v___x_5551_);
                                                                                        v___x_5584_ = l_Lean_Name_str___override(v___x_5583_, v___x_5556_);
                                                                                        v___x_5585_ = l_Lean_Name_str___override(v___x_5584_, v_str_5548_);
                                                                                        v_c_5239_ = v___x_5585_;
                                                                                        v___y_5240_ = v_a_5189_;
                                                                                        state = 10;
                                                                                        continue;
                                                                                    }
                                                                                } else {
                                                                                    lean_dec_ref(
                                                                                        v_str_5548_,
                                                                                    );
                                                                                    v_args_5195_ = v_args_5547_;
                                                                                    v___y_5196_ =
                                                                                        v_a_5185_;
                                                                                    v___y_5197_ =
                                                                                        v_a_5186_;
                                                                                    v___y_5198_ =
                                                                                        v_a_5187_;
                                                                                    v___y_5199_ =
                                                                                        v_a_5188_;
                                                                                    v___y_5200_ =
                                                                                        v_a_5189_;
                                                                                    state = 2;
                                                                                    continue;
                                                                                }
                                                                            } else {
                                                                                lean_dec_ref(
                                                                                    v_str_5548_,
                                                                                );
                                                                                v_args_5195_ =
                                                                                    v_args_5547_;
                                                                                v___y_5196_ =
                                                                                    v_a_5185_;
                                                                                v___y_5197_ =
                                                                                    v_a_5186_;
                                                                                v___y_5198_ =
                                                                                    v_a_5187_;
                                                                                v___y_5199_ =
                                                                                    v_a_5188_;
                                                                                v___y_5200_ =
                                                                                    v_a_5189_;
                                                                                state = 2;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            lean_dec_ref(
                                                                                v_str_5548_,
                                                                            );
                                                                            v_args_5195_ =
                                                                                v_args_5547_;
                                                                            v___y_5196_ = v_a_5185_;
                                                                            v___y_5197_ = v_a_5186_;
                                                                            v___y_5198_ = v_a_5187_;
                                                                            v___y_5199_ = v_a_5188_;
                                                                            v___y_5200_ = v_a_5189_;
                                                                            state = 2;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_str_5548_);
                                                                        v_args_5195_ = v_args_5547_;
                                                                        v___y_5196_ = v_a_5185_;
                                                                        v___y_5197_ = v_a_5186_;
                                                                        v___y_5198_ = v_a_5187_;
                                                                        v___y_5199_ = v_a_5188_;
                                                                        v___y_5200_ = v_a_5189_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_str_5548_);
                                                                    v_args_5195_ = v_args_5547_;
                                                                    v___y_5196_ = v_a_5185_;
                                                                    v___y_5197_ = v_a_5186_;
                                                                    v___y_5198_ = v_a_5187_;
                                                                    v___y_5199_ = v_a_5188_;
                                                                    v___y_5200_ = v_a_5189_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_str_5548_);
                                                                v_args_5195_ = v_args_5547_;
                                                                v___y_5196_ = v_a_5185_;
                                                                v___y_5197_ = v_a_5186_;
                                                                v___y_5198_ = v_a_5187_;
                                                                v___y_5199_ = v_a_5188_;
                                                                v___y_5200_ = v_a_5189_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_str_5548_);
                                                            v_args_5195_ = v_args_5547_;
                                                            v___y_5196_ = v_a_5185_;
                                                            v___y_5197_ = v_a_5186_;
                                                            v___y_5198_ = v_a_5187_;
                                                            v___y_5199_ = v_a_5188_;
                                                            v___y_5200_ = v_a_5189_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_str_5548_);
                                                        v_args_5195_ = v_args_5547_;
                                                        v___y_5196_ = v_a_5185_;
                                                        v___y_5197_ = v_a_5186_;
                                                        v___y_5198_ = v_a_5187_;
                                                        v___y_5199_ = v_a_5188_;
                                                        v___y_5200_ = v_a_5189_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                        _ => {
                                            v_args_5586_ = lean_ctor_get(v_e_5184_, 1);
                                            lean_inc_ref(v_args_5586_);
                                            lean_dec_ref_known(v_e_5184_, 2);
                                            v___x_5587_ = lean_array_get_size(v_args_5586_);
                                            lean_dec_ref(v_args_5586_);
                                            v___x_5588_ = lean_unsigned_to_nat(0);
                                            v___x_5589_ = lean_nat_dec_eq(v___x_5587_, v___x_5588_);
                                            if v___x_5589_ == 0 {
                                                lean_dec_ref_known(v_fn_5340_, 2);
                                                state = 11;
                                                continue;
                                            } else {
                                                v_c_5239_ = v_fn_5340_;
                                                v___y_5240_ = v_a_5189_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    }
                                }
                                0 => {
                                    v_args_5590_ = lean_ctor_get(v_e_5184_, 1);
                                    lean_inc_ref(v_args_5590_);
                                    lean_dec_ref_known(v_e_5184_, 2);
                                    v_str_5591_ = lean_ctor_get(v_fn_5340_, 1);
                                    v_str_5592_ = lean_ctor_get(v_pre_5341_, 1);
                                    v___x_5593_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__17;
                                    v___x_5594_ = lean_string_dec_eq(v_str_5592_, v___x_5593_);
                                    if v___x_5594_ == 0 {
                                        v___x_5595_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__18;
                                        v___x_5596_ = lean_string_dec_eq(v_str_5592_, v___x_5595_);
                                        if v___x_5596_ == 0 {
                                            v___x_5597_ = lean_array_get_size(v_args_5590_);
                                            lean_dec_ref(v_args_5590_);
                                            v___x_5598_ = lean_unsigned_to_nat(0);
                                            v___x_5599_ = lean_nat_dec_eq(v___x_5597_, v___x_5598_);
                                            if v___x_5599_ == 0 {
                                                lean_dec_ref_known(v_fn_5340_, 2);
                                                state = 11;
                                                continue;
                                            } else {
                                                v_c_5239_ = v_fn_5340_;
                                                v___y_5240_ = v_a_5189_;
                                                state = 10;
                                                continue;
                                            }
                                        } else {
                                            lean_inc_ref(v_str_5591_);
                                            lean_inc(v_pre_5342_);
                                            lean_dec_ref_known(v_fn_5340_, 2);
                                            v___x_5600_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__19;
                                            v___x_5601_ =
                                                lean_string_dec_eq(v_str_5591_, v___x_5600_);
                                            if v___x_5601_ == 0 {
                                                v___x_5602_ = lean_array_get_size(v_args_5590_);
                                                lean_dec_ref(v_args_5590_);
                                                v___x_5603_ = lean_unsigned_to_nat(0);
                                                v___x_5604_ =
                                                    lean_nat_dec_eq(v___x_5602_, v___x_5603_);
                                                if v___x_5604_ == 0 {
                                                    lean_dec_ref(v_str_5591_);
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    v___x_5605_ = l_Lean_Name_str___override(
                                                        v_pre_5342_,
                                                        v___x_5595_,
                                                    );
                                                    v___x_5606_ = l_Lean_Name_str___override(
                                                        v___x_5605_,
                                                        v_str_5591_,
                                                    );
                                                    v_c_5239_ = v___x_5606_;
                                                    v___y_5240_ = v_a_5189_;
                                                    state = 10;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_str_5591_);
                                                v___x_5607_ = lean_array_get_size(v_args_5590_);
                                                v___x_5608_ = lean_unsigned_to_nat(1);
                                                v___x_5609_ =
                                                    lean_nat_dec_eq(v___x_5607_, v___x_5608_);
                                                if v___x_5609_ == 0 {
                                                    lean_dec_ref(v_args_5590_);
                                                    v___x_5610_ = lean_unsigned_to_nat(0);
                                                    v___x_5611_ =
                                                        lean_nat_dec_eq(v___x_5607_, v___x_5610_);
                                                    if v___x_5611_ == 0 {
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        v___x_5612_ = l_Lean_Name_str___override(
                                                            v_pre_5342_,
                                                            v___x_5595_,
                                                        );
                                                        v___x_5613_ = l_Lean_Name_str___override(
                                                            v___x_5612_,
                                                            v___x_5600_,
                                                        );
                                                        v_c_5239_ = v___x_5613_;
                                                        v___y_5240_ = v_a_5189_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    v___x_5614_ = lean_unsigned_to_nat(0);
                                                    v___x_5615_ =
                                                        lean_array_fget(v_args_5590_, v___x_5614_);
                                                    lean_dec_ref(v_args_5590_);
                                                    if lean_obj_tag(v___x_5615_) == 1 {
                                                        v_fvarId_5616_ =
                                                            lean_ctor_get(v___x_5615_, 0);
                                                        v_isSharedCheck_5700_ =
                                                            (!lean_is_exclusive(v___x_5615_)) as u8;
                                                        if v_isSharedCheck_5700_ == 0 {
                                                            v___x_5618_ = v___x_5615_;
                                                            v_isShared_5619_ =
                                                                v_isSharedCheck_5700_;
                                                            state = 57;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_fvarId_5616_);
                                                            lean_dec(v___x_5615_);
                                                            v___x_5618_ = lean_box(0);
                                                            v_isShared_5619_ =
                                                                v_isSharedCheck_5700_;
                                                            state = 57;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v___x_5615_);
                                                        state = 11;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        lean_inc_ref(v_str_5591_);
                                        lean_inc(v_pre_5342_);
                                        lean_dec_ref_known(v_fn_5340_, 2);
                                        v___x_5701_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__20;
                                        v___x_5702_ = lean_string_dec_eq(v_str_5591_, v___x_5701_);
                                        if v___x_5702_ == 0 {
                                            v___x_5703_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__21;
                                            v___x_5704_ =
                                                lean_string_dec_eq(v_str_5591_, v___x_5703_);
                                            if v___x_5704_ == 0 {
                                                v___x_5705_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__22;
                                                v___x_5706_ =
                                                    lean_string_dec_eq(v_str_5591_, v___x_5705_);
                                                if v___x_5706_ == 0 {
                                                    v___x_5707_ = lean_array_get_size(v_args_5590_);
                                                    lean_dec_ref(v_args_5590_);
                                                    v___x_5708_ = lean_unsigned_to_nat(0);
                                                    v___x_5709_ =
                                                        lean_nat_dec_eq(v___x_5707_, v___x_5708_);
                                                    if v___x_5709_ == 0 {
                                                        lean_dec_ref(v_str_5591_);
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        v___x_5710_ = l_Lean_Name_str___override(
                                                            v_pre_5342_,
                                                            v___x_5593_,
                                                        );
                                                        v___x_5711_ = l_Lean_Name_str___override(
                                                            v___x_5710_,
                                                            v_str_5591_,
                                                        );
                                                        v_c_5239_ = v___x_5711_;
                                                        v___y_5240_ = v_a_5189_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_str_5591_);
                                                    v___x_5712_ = lean_array_get_size(v_args_5590_);
                                                    v___x_5713_ = lean_unsigned_to_nat(3);
                                                    v___x_5714_ =
                                                        lean_nat_dec_eq(v___x_5712_, v___x_5713_);
                                                    if v___x_5714_ == 0 {
                                                        lean_dec_ref(v_args_5590_);
                                                        v___x_5715_ = lean_unsigned_to_nat(0);
                                                        v___x_5716_ = lean_nat_dec_eq(
                                                            v___x_5712_,
                                                            v___x_5715_,
                                                        );
                                                        if v___x_5716_ == 0 {
                                                            state = 11;
                                                            continue;
                                                        } else {
                                                            v___x_5717_ =
                                                                l_Lean_Name_str___override(
                                                                    v_pre_5342_,
                                                                    v___x_5593_,
                                                                );
                                                            v___x_5718_ =
                                                                l_Lean_Name_str___override(
                                                                    v___x_5717_,
                                                                    v___x_5705_,
                                                                );
                                                            v_c_5239_ = v___x_5718_;
                                                            v___y_5240_ = v_a_5189_;
                                                            state = 10;
                                                            continue;
                                                        }
                                                    } else {
                                                        v___x_5719_ = lean_unsigned_to_nat(0);
                                                        v___x_5720_ = lean_array_fget_borrowed(
                                                            v_args_5590_,
                                                            v___x_5719_,
                                                        );
                                                        if lean_obj_tag(v___x_5720_) == 0 {
                                                            v___x_5721_ = lean_unsigned_to_nat(1);
                                                            v___x_5722_ = lean_array_fget(
                                                                v_args_5590_,
                                                                v___x_5721_,
                                                            );
                                                            if lean_obj_tag(v___x_5722_) == 1 {
                                                                v_fvarId_5723_ =
                                                                    lean_ctor_get(v___x_5722_, 0);
                                                                v_isSharedCheck_5776_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_5722_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_5776_ == 0 {
                                                                    v___x_5725_ = v___x_5722_;
                                                                    v_isShared_5726_ =
                                                                        v_isSharedCheck_5776_;
                                                                    state = 74;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_fvarId_5723_);
                                                                    lean_dec(v___x_5722_);
                                                                    v___x_5725_ = lean_box(0);
                                                                    v_isShared_5726_ =
                                                                        v_isSharedCheck_5776_;
                                                                    state = 74;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec(v___x_5722_);
                                                                lean_dec_ref(v_args_5590_);
                                                                state = 11;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_args_5590_);
                                                            state = 11;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_str_5591_);
                                                v___x_5777_ = lean_array_get_size(v_args_5590_);
                                                v___x_5778_ = lean_unsigned_to_nat(2);
                                                v___x_5779_ =
                                                    lean_nat_dec_eq(v___x_5777_, v___x_5778_);
                                                if v___x_5779_ == 0 {
                                                    lean_dec_ref(v_args_5590_);
                                                    v___x_5780_ = lean_unsigned_to_nat(0);
                                                    v___x_5781_ =
                                                        lean_nat_dec_eq(v___x_5777_, v___x_5780_);
                                                    if v___x_5781_ == 0 {
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        v___x_5782_ = l_Lean_Name_str___override(
                                                            v_pre_5342_,
                                                            v___x_5593_,
                                                        );
                                                        v___x_5783_ = l_Lean_Name_str___override(
                                                            v___x_5782_,
                                                            v___x_5703_,
                                                        );
                                                        v_c_5239_ = v___x_5783_;
                                                        v___y_5240_ = v_a_5189_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    v___x_5784_ = lean_unsigned_to_nat(0);
                                                    v___x_5785_ = lean_array_fget_borrowed(
                                                        v_args_5590_,
                                                        v___x_5784_,
                                                    );
                                                    if lean_obj_tag(v___x_5785_) == 0 {
                                                        v___x_5786_ = lean_unsigned_to_nat(1);
                                                        v___x_5787_ = lean_array_fget(
                                                            v_args_5590_,
                                                            v___x_5786_,
                                                        );
                                                        lean_dec_ref(v_args_5590_);
                                                        if lean_obj_tag(v___x_5787_) == 1 {
                                                            v_fvarId_5788_ =
                                                                lean_ctor_get(v___x_5787_, 0);
                                                            lean_inc(v_fvarId_5788_);
                                                            lean_dec_ref_known(v___x_5787_, 1);
                                                            v_sizeId_5259_ = v_fvarId_5788_;
                                                            v___y_5260_ = v_a_5185_;
                                                            state = 14;
                                                            continue;
                                                        } else {
                                                            lean_dec(v___x_5787_);
                                                            state = 11;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_args_5590_);
                                                        state = 11;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_str_5591_);
                                            v___x_5789_ = lean_array_get_size(v_args_5590_);
                                            v___x_5790_ = lean_unsigned_to_nat(2);
                                            v___x_5791_ = lean_nat_dec_eq(v___x_5789_, v___x_5790_);
                                            if v___x_5791_ == 0 {
                                                lean_dec_ref(v_args_5590_);
                                                v___x_5792_ = lean_unsigned_to_nat(0);
                                                v___x_5793_ =
                                                    lean_nat_dec_eq(v___x_5789_, v___x_5792_);
                                                if v___x_5793_ == 0 {
                                                    state = 11;
                                                    continue;
                                                } else {
                                                    v___x_5794_ = l_Lean_Name_str___override(
                                                        v_pre_5342_,
                                                        v___x_5593_,
                                                    );
                                                    v___x_5795_ = l_Lean_Name_str___override(
                                                        v___x_5794_,
                                                        v___x_5701_,
                                                    );
                                                    v_c_5239_ = v___x_5795_;
                                                    v___y_5240_ = v_a_5189_;
                                                    state = 10;
                                                    continue;
                                                }
                                            } else {
                                                v___x_5796_ = lean_unsigned_to_nat(0);
                                                v___x_5797_ = lean_array_fget_borrowed(
                                                    v_args_5590_,
                                                    v___x_5796_,
                                                );
                                                if lean_obj_tag(v___x_5797_) == 0 {
                                                    v___x_5798_ = lean_unsigned_to_nat(1);
                                                    v___x_5799_ =
                                                        lean_array_fget(v_args_5590_, v___x_5798_);
                                                    lean_dec_ref(v_args_5590_);
                                                    if lean_obj_tag(v___x_5799_) == 1 {
                                                        v_fvarId_5800_ =
                                                            lean_ctor_get(v___x_5799_, 0);
                                                        lean_inc(v_fvarId_5800_);
                                                        lean_dec_ref_known(v___x_5799_, 1);
                                                        v_sizeId_5259_ = v_fvarId_5800_;
                                                        v___y_5260_ = v_a_5185_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        lean_dec(v___x_5799_);
                                                        state = 11;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_args_5590_);
                                                    state = 11;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                                _ => {
                                    v_args_5801_ = lean_ctor_get(v_e_5184_, 1);
                                    lean_inc_ref(v_args_5801_);
                                    lean_dec_ref_known(v_e_5184_, 2);
                                    v___x_5802_ = lean_array_get_size(v_args_5801_);
                                    lean_dec_ref(v_args_5801_);
                                    v___x_5803_ = lean_unsigned_to_nat(0);
                                    v___x_5804_ = lean_nat_dec_eq(v___x_5802_, v___x_5803_);
                                    if v___x_5804_ == 0 {
                                        lean_dec_ref_known(v_fn_5340_, 2);
                                        state = 11;
                                        continue;
                                    } else {
                                        v_c_5239_ = v_fn_5340_;
                                        v___y_5240_ = v_a_5189_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_args_5805_ = lean_ctor_get(v_e_5184_, 1);
                            lean_inc_ref(v_args_5805_);
                            lean_dec_ref_known(v_e_5184_, 2);
                            v___x_5806_ = lean_array_get_size(v_args_5805_);
                            lean_dec_ref(v_args_5805_);
                            v___x_5807_ = lean_unsigned_to_nat(0);
                            v___x_5808_ = lean_nat_dec_eq(v___x_5806_, v___x_5807_);
                            if v___x_5808_ == 0 {
                                lean_dec_ref_known(v_fn_5340_, 2);
                                state = 11;
                                continue;
                            } else {
                                v_c_5239_ = v_fn_5340_;
                                v___y_5240_ = v_a_5189_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_args_5809_ = lean_ctor_get(v_e_5184_, 1);
                        lean_inc_ref(v_args_5809_);
                        lean_dec_ref_known(v_e_5184_, 2);
                        v___x_5810_ = lean_array_get_size(v_args_5809_);
                        lean_dec_ref(v_args_5809_);
                        v___x_5811_ = lean_unsigned_to_nat(0);
                        v___x_5812_ = lean_nat_dec_eq(v___x_5810_, v___x_5811_);
                        if v___x_5812_ == 0 {
                            lean_dec(v_fn_5340_);
                            state = 11;
                            continue;
                        } else {
                            v_c_5239_ = v_fn_5340_;
                            v___y_5240_ = v_a_5189_;
                            state = 10;
                            continue;
                        }
                    }
                }
                13 => {
                    v_fvarId_5813_ = lean_ctor_get(v_e_5184_, 1);
                    lean_inc(v_fvarId_5813_);
                    lean_dec_ref_known(v_e_5184_, 2);
                    v___x_5814_ = lean_st_ref_get(v_a_5185_);
                    v___x_5815_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_5814_, v_fvarId_5813_);
                    lean_dec(v_fvarId_5813_);
                    lean_dec(v___x_5814_);
                    match lean_obj_tag(v___x_5815_) {
                        3 => {
                            lean_dec_ref_known(v___x_5815_, 0);
                            v___x_5816_ = lean_box(0);
                            v___x_5817_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5817_, 0, v___x_5816_);
                            return v___x_5817_;
                        }
                        4 => {
                            v_val_5818_ = lean_ctor_get_uint64(v___x_5815_, 0 as u32);
                            lean_dec_ref_known(v___x_5815_, 0);
                            v___x_5819_ = lean_unsigned_to_nat(0);
                            v___x_5820_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__0;
                            v___x_5821_ = l_Lean_Compiler_LCNF_uint64ToByteArrayLE(v_val_5818_);
                            v___x_5822_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_5822_, 0, v___x_5819_);
                            lean_ctor_set(v___x_5822_, 1, v___x_5820_);
                            lean_ctor_set(v___x_5822_, 2, v___x_5820_);
                            lean_ctor_set(v___x_5822_, 3, v___x_5821_);
                            v___x_5823_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5823_, 0, v___x_5822_);
                            v___x_5824_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5824_, 0, v___x_5823_);
                            return v___x_5824_;
                        }
                        5 => {
                            v_val_5825_ = lean_ctor_get_uint64(v___x_5815_, 0 as u32);
                            lean_dec_ref_known(v___x_5815_, 0);
                            v___x_5826_ = lean_unsigned_to_nat(0);
                            v___x_5827_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__0;
                            v___x_5828_ = lean_unsigned_to_nat(1);
                            v___x_5829_ = lean_mk_empty_array_with_capacity(v___x_5828_);
                            v___x_5830_ = lean_box_uint64(v_val_5825_);
                            v___x_5831_ = lean_array_push(v___x_5829_, v___x_5830_);
                            v___x_5832_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_5832_, 0, v___x_5826_);
                            lean_ctor_set(v___x_5832_, 1, v___x_5827_);
                            lean_ctor_set(v___x_5832_, 2, v___x_5831_);
                            lean_ctor_set(v___x_5832_, 3, v___x_5827_);
                            v___x_5833_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_5833_, 0, v___x_5832_);
                            v___x_5834_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5834_, 0, v___x_5833_);
                            return v___x_5834_;
                        }
                        1 => {
                            lean_dec_ref_known(v___x_5815_, 0);
                            v___x_5835_ = lean_box(0);
                            v___x_5836_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5836_, 0, v___x_5835_);
                            return v___x_5836_;
                        }
                        2 => {
                            lean_dec_ref_known(v___x_5815_, 0);
                            v___x_5837_ = lean_box(0);
                            v___x_5838_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5838_, 0, v___x_5837_);
                            return v___x_5838_;
                        }
                        _ => {
                            lean_dec_ref(v___x_5815_);
                            v___x_5839_ = lean_box(0);
                            v___x_5840_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5840_, 0, v___x_5839_);
                            return v___x_5840_;
                        }
                    }
                }
                10 => {
                    v_fn_5841_ = lean_ctor_get(v_e_5184_, 0);
                    v_args_5842_ = lean_ctor_get(v_e_5184_, 1);
                    v_isSharedCheck_5878_ = (!lean_is_exclusive(v_e_5184_)) as u8;
                    if v_isSharedCheck_5878_ == 0 {
                        v___x_5844_ = v_e_5184_;
                        v_isShared_5845_ = v_isSharedCheck_5878_;
                        state = 85;
                        continue;
                    } else {
                        lean_inc(v_args_5842_);
                        lean_inc(v_fn_5841_);
                        lean_dec(v_e_5184_);
                        v___x_5844_ = lean_box(0);
                        v_isShared_5845_ = v_isSharedCheck_5878_;
                        state = 85;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_e_5184_);
                    state = 11;
                    continue;
                }
            },
            1 => {
                v___x_5192_ = lean_box(0);
                v___x_5193_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5193_, 0, v___x_5192_);
                return v___x_5193_;
            }
            2 => {
                v_nameAcc_5201_ = lean_box(0);
                v___x_5202_ = lean_array_get_size(v_args_5195_);
                v_processedArgs_5203_ = lean_mk_empty_array_with_capacity(v___x_5202_);
                v___x_5204_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5204_, 0, v_nameAcc_5201_);
                lean_ctor_set(v___x_5204_, 1, v_processedArgs_5203_);
                v_sz_5205_ = lean_array_size(v_args_5195_);
                v___x_5206_ = 0usize;
                v___x_5207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0___redArg(v_args_5195_, v_sz_5205_, v___x_5206_, v___x_5204_, v___y_5196_, v___y_5200_);
                lean_dec_ref(v_args_5195_);
                if lean_obj_tag(v___x_5207_) == 0 {
                    v_a_5208_ = lean_ctor_get(v___x_5207_, 0);
                    v_isSharedCheck_5229_ = (!lean_is_exclusive(v___x_5207_)) as u8;
                    if v_isSharedCheck_5229_ == 0 {
                        v___x_5210_ = v___x_5207_;
                        v_isShared_5211_ = v_isSharedCheck_5229_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5208_);
                        lean_dec(v___x_5207_);
                        v___x_5210_ = lean_box(0);
                        v_isShared_5211_ = v_isSharedCheck_5229_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5230_ = lean_ctor_get(v___x_5207_, 0);
                    v_isSharedCheck_5237_ = (!lean_is_exclusive(v___x_5207_)) as u8;
                    if v_isSharedCheck_5237_ == 0 {
                        v___x_5232_ = v___x_5207_;
                        v_isShared_5233_ = v_isSharedCheck_5237_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5230_);
                        lean_dec(v___x_5207_);
                        v___x_5232_ = lean_box(0);
                        v_isShared_5233_ = v_isSharedCheck_5237_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_5208_) == 0 {
                    v___x_5212_ = lean_box(0);
                    if v_isShared_5211_ == 0 {
                        lean_ctor_set(v___x_5210_, 0, v___x_5212_);
                        v___x_5214_ = v___x_5210_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5215_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5215_, 0, v___x_5212_);
                        v___x_5214_ = v_reuseFailAlloc_5215_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_5216_ = lean_ctor_get(v_a_5208_, 0);
                    v_isSharedCheck_5228_ = (!lean_is_exclusive(v_a_5208_)) as u8;
                    if v_isSharedCheck_5228_ == 0 {
                        v___x_5218_ = v_a_5208_;
                        v_isShared_5219_ = v_isSharedCheck_5228_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_5216_);
                        lean_dec(v_a_5208_);
                        v___x_5218_ = lean_box(0);
                        v_isShared_5219_ = v_isSharedCheck_5228_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5214_;
            }
            5 => {
                v_snd_5220_ = lean_ctor_get(v_val_5216_, 1);
                lean_inc(v_snd_5220_);
                lean_dec(v_val_5216_);
                v___x_5221_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5221_, 0, v_snd_5220_);
                if v_isShared_5219_ == 0 {
                    lean_ctor_set(v___x_5218_, 0, v___x_5221_);
                    v___x_5223_ = v___x_5218_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5221_);
                    v___x_5223_ = v_reuseFailAlloc_5227_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5211_ == 0 {
                    lean_ctor_set(v___x_5210_, 0, v___x_5223_);
                    v___x_5225_ = v___x_5210_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5223_);
                    v___x_5225_ = v_reuseFailAlloc_5226_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5225_;
            }
            8 => {
                if v_isShared_5233_ == 0 {
                    v___x_5235_ = v___x_5232_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5236_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5230_);
                    v___x_5235_ = v_reuseFailAlloc_5236_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5235_;
            }
            10 => {
                v___x_5241_ = lean_st_ref_get(v___y_5240_);
                v_env_5242_ = lean_ctor_get(v___x_5241_, 0);
                lean_inc_ref(v_env_5242_);
                lean_dec(v___x_5241_);
                v___x_5243_ = l_Lean_Compiler_LCNF_isSimpleGroundDecl(v_env_5242_, v_c_5239_);
                if v___x_5243_ == 0 {
                    lean_dec(v_c_5239_);
                    v___x_5244_ = lean_box(0);
                    v___x_5245_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5245_, 0, v___x_5244_);
                    return v___x_5245_;
                } else {
                    v___x_5246_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v___x_5246_, 0, v_c_5239_);
                    v___x_5247_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5247_, 0, v___x_5246_);
                    v___x_5248_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5248_, 0, v___x_5247_);
                    return v___x_5248_;
                }
            }
            11 => {
                v___x_5250_ = lean_box(0);
                v___x_5251_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5251_, 0, v___x_5250_);
                return v___x_5251_;
            }
            12 => {
                v___x_5253_ = lean_box(0);
                v___x_5254_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5254_, 0, v___x_5253_);
                return v___x_5254_;
            }
            13 => {
                v___x_5256_ = lean_box(0);
                v___x_5257_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5257_, 0, v___x_5256_);
                return v___x_5257_;
            }
            14 => {
                v___x_5261_ = lean_st_ref_get(v___y_5260_);
                v___x_5262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_5261_, v_sizeId_5259_);
                lean_dec(v_sizeId_5259_);
                lean_dec(v___x_5261_);
                if lean_obj_tag(v___x_5262_) == 0 {
                    v_arg_5263_ = lean_ctor_get(v___x_5262_, 0);
                    lean_inc_ref(v_arg_5263_);
                    lean_dec_ref_known(v___x_5262_, 1);
                    if lean_obj_tag(v_arg_5263_) == 0 {
                        v_val_5264_ = lean_ctor_get(v_arg_5263_, 0);
                        v_isSharedCheck_5274_ = (!lean_is_exclusive(v_arg_5263_)) as u8;
                        if v_isSharedCheck_5274_ == 0 {
                            v___x_5266_ = v_arg_5263_;
                            v_isShared_5267_ = v_isSharedCheck_5274_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_val_5264_);
                            lean_dec(v_arg_5263_);
                            v___x_5266_ = lean_box(0);
                            v_isShared_5267_ = v_isSharedCheck_5274_;
                            state = 15;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_5263_);
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_5262_);
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_5268_ = lean_unsigned_to_nat(0);
                v___x_5269_ = lean_nat_dec_eq(v_val_5264_, v___x_5268_);
                lean_dec(v_val_5264_);
                if v___x_5269_ == 0 {
                    lean_del_object(v___x_5266_);
                    state = 13;
                    continue;
                } else {
                    v___x_5270_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__2;
                    if v_isShared_5267_ == 0 {
                        lean_ctor_set(v___x_5266_, 0, v___x_5270_);
                        v___x_5272_ = v___x_5266_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
                        v___x_5272_ = v_reuseFailAlloc_5273_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_5272_;
            }
            17 => {
                if lean_obj_tag(v_value_5275_) == 1 {
                    v_val_5279_ = lean_ctor_get(v_value_5275_, 0);
                    v_isSharedCheck_5290_ = (!lean_is_exclusive(v_value_5275_)) as u8;
                    if v_isSharedCheck_5290_ == 0 {
                        v___x_5281_ = v_value_5275_;
                        v_isShared_5282_ = v_isSharedCheck_5290_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_val_5279_);
                        lean_dec(v_value_5275_);
                        v___x_5281_ = lean_box(0);
                        v_isShared_5282_ = v_isSharedCheck_5290_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_5275_);
                    v___x_5291_ = lean_box(0);
                    if v_isShared_5278_ == 0 {
                        lean_ctor_set(v___x_5277_, 0, v___x_5291_);
                        v___x_5293_ = v___x_5277_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_5294_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5294_, 0, v___x_5291_);
                        v___x_5293_ = v_reuseFailAlloc_5294_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_5282_ == 0 {
                    v___x_5284_ = v___x_5281_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5289_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5289_, 0, v_val_5279_);
                    v___x_5284_ = v_reuseFailAlloc_5289_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_5278_ == 0 {
                    lean_ctor_set_tag(v___x_5277_, 1);
                    lean_ctor_set(v___x_5277_, 0, v___x_5284_);
                    v___x_5286_ = v___x_5277_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5288_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5284_);
                    v___x_5286_ = v_reuseFailAlloc_5288_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_5287_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5287_, 0, v___x_5286_);
                return v___x_5287_;
            }
            21 => {
                return v___x_5293_;
            }
            22 => {
                if v___y_5302_ == 0 {
                    lean_dec(v_cidx_5298_);
                    lean_dec_ref(v_args_5297_);
                    state = 12;
                    continue;
                } else {
                    v___x_5303_ = lean_array_get_size(v_args_5297_);
                    v___x_5304_ = lean_unsigned_to_nat(0);
                    v___x_5305_ = lean_nat_dec_eq(v___x_5303_, v___x_5304_);
                    if v___x_5305_ == 0 {
                        v___x_5306_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs(v_args_5297_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
                        if lean_obj_tag(v___x_5306_) == 0 {
                            v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
                            v_isSharedCheck_5328_ = (!lean_is_exclusive(v___x_5306_)) as u8;
                            if v_isSharedCheck_5328_ == 0 {
                                v___x_5309_ = v___x_5306_;
                                v_isShared_5310_ = v_isSharedCheck_5328_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_5307_);
                                lean_dec(v___x_5306_);
                                v___x_5309_ = lean_box(0);
                                v_isShared_5310_ = v_isSharedCheck_5328_;
                                state = 23;
                                continue;
                            }
                        } else {
                            lean_dec(v_cidx_5298_);
                            v_a_5329_ = lean_ctor_get(v___x_5306_, 0);
                            v_isSharedCheck_5336_ = (!lean_is_exclusive(v___x_5306_)) as u8;
                            if v_isSharedCheck_5336_ == 0 {
                                v___x_5331_ = v___x_5306_;
                                v_isShared_5332_ = v_isSharedCheck_5336_;
                                state = 28;
                                continue;
                            } else {
                                lean_inc(v_a_5329_);
                                lean_dec(v___x_5306_);
                                v___x_5331_ = lean_box(0);
                                v_isShared_5332_ = v_isSharedCheck_5336_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_cidx_5298_);
                        lean_dec_ref(v_args_5297_);
                        state = 12;
                        continue;
                    }
                }
            }
            23 => {
                if lean_obj_tag(v_a_5307_) == 0 {
                    lean_dec(v_cidx_5298_);
                    v___x_5311_ = lean_box(0);
                    if v_isShared_5310_ == 0 {
                        lean_ctor_set(v___x_5309_, 0, v___x_5311_);
                        v___x_5313_ = v___x_5309_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5311_);
                        v___x_5313_ = v_reuseFailAlloc_5314_;
                        state = 24;
                        continue;
                    }
                } else {
                    v_val_5315_ = lean_ctor_get(v_a_5307_, 0);
                    v_isSharedCheck_5327_ = (!lean_is_exclusive(v_a_5307_)) as u8;
                    if v_isSharedCheck_5327_ == 0 {
                        v___x_5317_ = v_a_5307_;
                        v_isShared_5318_ = v_isSharedCheck_5327_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_val_5315_);
                        lean_dec(v_a_5307_);
                        v___x_5317_ = lean_box(0);
                        v_isShared_5318_ = v_isSharedCheck_5327_;
                        state = 25;
                        continue;
                    }
                }
            }
            24 => {
                return v___x_5313_;
            }
            25 => {
                v___x_5319_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__3;
                v___x_5320_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5320_, 0, v_cidx_5298_);
                lean_ctor_set(v___x_5320_, 1, v_val_5315_);
                lean_ctor_set(v___x_5320_, 2, v___x_5319_);
                lean_ctor_set(v___x_5320_, 3, v___x_5319_);
                if v_isShared_5318_ == 0 {
                    lean_ctor_set(v___x_5317_, 0, v___x_5320_);
                    v___x_5322_ = v___x_5317_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5320_);
                    v___x_5322_ = v_reuseFailAlloc_5326_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_5310_ == 0 {
                    lean_ctor_set(v___x_5309_, 0, v___x_5322_);
                    v___x_5324_ = v___x_5309_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_5324_;
            }
            28 => {
                if v_isShared_5332_ == 0 {
                    v___x_5334_ = v___x_5331_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
                    v___x_5334_ = v_reuseFailAlloc_5335_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5334_;
            }
            30 => {
                if lean_obj_tag(v_a_5388_) == 0 {
                    lean_dec_ref(v_args_5345_);
                    v___x_5392_ = lean_box(0);
                    if v_isShared_5391_ == 0 {
                        lean_ctor_set(v___x_5390_, 0, v___x_5392_);
                        v___x_5394_ = v___x_5390_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5395_, 0, v___x_5392_);
                        v___x_5394_ = v_reuseFailAlloc_5395_;
                        state = 31;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5390_);
                    v_val_5396_ = lean_ctor_get(v_a_5388_, 0);
                    v_isSharedCheck_5459_ = (!lean_is_exclusive(v_a_5388_)) as u8;
                    if v_isSharedCheck_5459_ == 0 {
                        v___x_5398_ = v_a_5388_;
                        v_isShared_5399_ = v_isSharedCheck_5459_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_val_5396_);
                        lean_dec(v_a_5388_);
                        v___x_5398_ = lean_box(0);
                        v_isShared_5399_ = v_isSharedCheck_5459_;
                        state = 32;
                        continue;
                    }
                }
            }
            31 => {
                return v___x_5394_;
            }
            32 => {
                v___x_5400_ = lean_unsigned_to_nat(1);
                v___x_5401_ = lean_array_get(v___x_5384_, v_args_5345_, v___x_5400_);
                lean_dec_ref(v_args_5345_);
                v___x_5402_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileStrArg___redArg(v___x_5401_, v_a_5185_, v_a_5189_);
                v_a_5403_ = lean_ctor_get(v___x_5402_, 0);
                v_isSharedCheck_5458_ = (!lean_is_exclusive(v___x_5402_)) as u8;
                if v_isSharedCheck_5458_ == 0 {
                    v___x_5405_ = v___x_5402_;
                    v_isShared_5406_ = v_isSharedCheck_5458_;
                    state = 33;
                    continue;
                } else {
                    lean_inc(v_a_5403_);
                    lean_dec(v___x_5402_);
                    v___x_5405_ = lean_box(0);
                    v_isShared_5406_ = v_isSharedCheck_5458_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                if lean_obj_tag(v_a_5403_) == 0 {
                    lean_del_object(v___x_5398_);
                    lean_dec(v_val_5396_);
                    v___x_5407_ = lean_box(0);
                    if v_isShared_5406_ == 0 {
                        lean_ctor_set(v___x_5405_, 0, v___x_5407_);
                        v___x_5409_ = v___x_5405_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5407_);
                        v___x_5409_ = v_reuseFailAlloc_5410_;
                        state = 34;
                        continue;
                    }
                } else {
                    v_val_5411_ = lean_ctor_get(v_a_5403_, 0);
                    v_isSharedCheck_5457_ = (!lean_is_exclusive(v_a_5403_)) as u8;
                    if v_isSharedCheck_5457_ == 0 {
                        v___x_5413_ = v_a_5403_;
                        v_isShared_5414_ = v_isSharedCheck_5457_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_val_5411_);
                        lean_dec(v_a_5403_);
                        v___x_5413_ = lean_box(0);
                        v_isShared_5414_ = v_isSharedCheck_5457_;
                        state = 35;
                        continue;
                    }
                }
            }
            34 => {
                return v___x_5409_;
            }
            35 => {
                v_fst_5415_ = lean_ctor_get(v_val_5411_, 0);
                lean_inc(v_fst_5415_);
                v_snd_5416_ = lean_ctor_get(v_val_5411_, 1);
                lean_inc(v_snd_5416_);
                lean_dec(v_val_5411_);
                lean_inc(v_val_5396_);
                v___x_5417_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral(v_val_5396_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
                if lean_obj_tag(v___x_5417_) == 0 {
                    v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
                    v_isSharedCheck_5448_ = (!lean_is_exclusive(v___x_5417_)) as u8;
                    if v_isSharedCheck_5448_ == 0 {
                        v___x_5420_ = v___x_5417_;
                        v_isShared_5421_ = v_isSharedCheck_5448_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_5418_);
                        lean_dec(v___x_5417_);
                        v___x_5420_ = lean_box(0);
                        v_isShared_5421_ = v_isSharedCheck_5448_;
                        state = 36;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_5416_);
                    lean_dec(v_fst_5415_);
                    lean_del_object(v___x_5413_);
                    lean_del_object(v___x_5405_);
                    lean_del_object(v___x_5398_);
                    lean_dec(v_val_5396_);
                    v_a_5449_ = lean_ctor_get(v___x_5417_, 0);
                    v_isSharedCheck_5456_ = (!lean_is_exclusive(v___x_5417_)) as u8;
                    if v_isSharedCheck_5456_ == 0 {
                        v___x_5451_ = v___x_5417_;
                        v_isShared_5452_ = v_isSharedCheck_5456_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_5449_);
                        lean_dec(v___x_5417_);
                        v___x_5451_ = lean_box(0);
                        v_isShared_5452_ = v_isSharedCheck_5456_;
                        state = 42;
                        continue;
                    }
                }
            }
            36 => {
                if lean_obj_tag(v_a_5418_) == 0 {
                    lean_del_object(v___x_5420_);
                    lean_dec(v_snd_5416_);
                    lean_dec(v_fst_5415_);
                    lean_del_object(v___x_5413_);
                    lean_del_object(v___x_5398_);
                    lean_dec(v_val_5396_);
                    v___x_5440_ = lean_box(0);
                    if v_isShared_5406_ == 0 {
                        lean_ctor_set(v___x_5405_, 0, v___x_5440_);
                        v___x_5442_ = v___x_5405_;
                        state = 41;
                        continue;
                    } else {
                        v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5443_, 0, v___x_5440_);
                        v___x_5442_ = v_reuseFailAlloc_5443_;
                        state = 41;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5405_);
                    v_val_5444_ = lean_ctor_get(v_a_5418_, 0);
                    lean_inc(v_val_5444_);
                    lean_dec_ref_known(v_a_5418_, 1);
                    v___x_5445_ = l_Lean_Name_str___override(v_val_5444_, v_snd_5416_);
                    if lean_obj_tag(v___x_5445_) == 0 {
                        v___x_5446_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0);
                        v___y_5423_ = v___x_5446_;
                        state = 37;
                        continue;
                    } else {
                        v_hash_5447_ = lean_ctor_get_uint64(
                            v___x_5445_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        lean_dec(v___x_5445_);
                        v___y_5423_ = v_hash_5447_;
                        state = 37;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_5399_ == 0 {
                    lean_ctor_set(v___x_5398_, 0, v_fst_5415_);
                    v___x_5425_ = v___x_5398_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5439_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_fst_5415_);
                    v___x_5425_ = v_reuseFailAlloc_5439_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_5426_ = lean_unsigned_to_nat(2);
                v___x_5427_ = lean_mk_empty_array_with_capacity(v___x_5426_);
                v___x_5428_ = lean_array_push(v___x_5427_, v_val_5396_);
                v___x_5429_ = lean_array_push(v___x_5428_, v___x_5425_);
                v___x_5430_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__3;
                v___x_5431_ = l_Lean_Compiler_LCNF_uint64ToByteArrayLE(v___y_5423_);
                v___x_5432_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5432_, 0, v___x_5400_);
                lean_ctor_set(v___x_5432_, 1, v___x_5429_);
                lean_ctor_set(v___x_5432_, 2, v___x_5430_);
                lean_ctor_set(v___x_5432_, 3, v___x_5431_);
                if v_isShared_5414_ == 0 {
                    lean_ctor_set(v___x_5413_, 0, v___x_5432_);
                    v___x_5434_ = v___x_5413_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_5438_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5432_);
                    v___x_5434_ = v_reuseFailAlloc_5438_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_5421_ == 0 {
                    lean_ctor_set(v___x_5420_, 0, v___x_5434_);
                    v___x_5436_ = v___x_5420_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5434_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5436_;
            }
            41 => {
                return v___x_5442_;
            }
            42 => {
                if v_isShared_5452_ == 0 {
                    v___x_5454_ = v___x_5451_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5455_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_a_5449_);
                    v___x_5454_ = v_reuseFailAlloc_5455_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_5454_;
            }
            44 => {
                if lean_obj_tag(v_a_5474_) == 0 {
                    lean_dec_ref(v_args_5345_);
                    v___x_5478_ = lean_box(0);
                    if v_isShared_5477_ == 0 {
                        lean_ctor_set(v___x_5476_, 0, v___x_5478_);
                        v___x_5480_ = v___x_5476_;
                        state = 45;
                        continue;
                    } else {
                        v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5481_, 0, v___x_5478_);
                        v___x_5480_ = v_reuseFailAlloc_5481_;
                        state = 45;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5476_);
                    v_val_5482_ = lean_ctor_get(v_a_5474_, 0);
                    lean_inc(v_val_5482_);
                    lean_dec_ref_known(v_a_5474_, 1);
                    v___x_5483_ = lean_unsigned_to_nat(1);
                    v___x_5484_ = lean_array_get(v___x_5470_, v_args_5345_, v___x_5483_);
                    lean_dec_ref(v_args_5345_);
                    v___x_5485_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArg___redArg(v___x_5484_, v_a_5185_);
                    v_a_5486_ = lean_ctor_get(v___x_5485_, 0);
                    v_isSharedCheck_5541_ = (!lean_is_exclusive(v___x_5485_)) as u8;
                    if v_isSharedCheck_5541_ == 0 {
                        v___x_5488_ = v___x_5485_;
                        v_isShared_5489_ = v_isSharedCheck_5541_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_a_5486_);
                        lean_dec(v___x_5485_);
                        v___x_5488_ = lean_box(0);
                        v_isShared_5489_ = v_isSharedCheck_5541_;
                        state = 46;
                        continue;
                    }
                }
            }
            45 => {
                return v___x_5480_;
            }
            46 => {
                if lean_obj_tag(v_a_5486_) == 0 {
                    lean_dec(v_val_5482_);
                    v___x_5490_ = lean_box(0);
                    if v_isShared_5489_ == 0 {
                        lean_ctor_set(v___x_5488_, 0, v___x_5490_);
                        v___x_5492_ = v___x_5488_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
                        v___x_5492_ = v_reuseFailAlloc_5493_;
                        state = 47;
                        continue;
                    }
                } else {
                    v_val_5494_ = lean_ctor_get(v_a_5486_, 0);
                    v_isSharedCheck_5540_ = (!lean_is_exclusive(v_a_5486_)) as u8;
                    if v_isSharedCheck_5540_ == 0 {
                        v___x_5496_ = v_a_5486_;
                        v_isShared_5497_ = v_isSharedCheck_5540_;
                        state = 48;
                        continue;
                    } else {
                        lean_inc(v_val_5494_);
                        lean_dec(v_a_5486_);
                        v___x_5496_ = lean_box(0);
                        v_isShared_5497_ = v_isSharedCheck_5540_;
                        state = 48;
                        continue;
                    }
                }
            }
            47 => {
                return v___x_5492_;
            }
            48 => {
                if lean_obj_tag(v_val_5494_) == 0 {
                    v_val_5498_ = lean_ctor_get(v_val_5494_, 0);
                    lean_inc(v_val_5482_);
                    v___x_5499_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_interpNameLiteral(v_val_5482_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
                    if lean_obj_tag(v___x_5499_) == 0 {
                        v_a_5500_ = lean_ctor_get(v___x_5499_, 0);
                        v_isSharedCheck_5527_ = (!lean_is_exclusive(v___x_5499_)) as u8;
                        if v_isSharedCheck_5527_ == 0 {
                            v___x_5502_ = v___x_5499_;
                            v_isShared_5503_ = v_isSharedCheck_5527_;
                            state = 49;
                            continue;
                        } else {
                            lean_inc(v_a_5500_);
                            lean_dec(v___x_5499_);
                            v___x_5502_ = lean_box(0);
                            v_isShared_5503_ = v_isSharedCheck_5527_;
                            state = 49;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_val_5494_, 1);
                        lean_del_object(v___x_5496_);
                        lean_del_object(v___x_5488_);
                        lean_dec(v_val_5482_);
                        v_a_5528_ = lean_ctor_get(v___x_5499_, 0);
                        v_isSharedCheck_5535_ = (!lean_is_exclusive(v___x_5499_)) as u8;
                        if v_isSharedCheck_5535_ == 0 {
                            v___x_5530_ = v___x_5499_;
                            v_isShared_5531_ = v_isSharedCheck_5535_;
                            state = 54;
                            continue;
                        } else {
                            lean_inc(v_a_5528_);
                            lean_dec(v___x_5499_);
                            v___x_5530_ = lean_box(0);
                            v_isShared_5531_ = v_isSharedCheck_5535_;
                            state = 54;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5496_);
                    lean_dec(v_val_5494_);
                    lean_dec(v_val_5482_);
                    v___x_5536_ = lean_box(0);
                    if v_isShared_5489_ == 0 {
                        lean_ctor_set(v___x_5488_, 0, v___x_5536_);
                        v___x_5538_ = v___x_5488_;
                        state = 56;
                        continue;
                    } else {
                        v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
                        v___x_5538_ = v_reuseFailAlloc_5539_;
                        state = 56;
                        continue;
                    }
                }
            }
            49 => {
                if lean_obj_tag(v_a_5500_) == 0 {
                    lean_del_object(v___x_5502_);
                    lean_dec_ref_known(v_val_5494_, 1);
                    lean_del_object(v___x_5496_);
                    lean_dec(v_val_5482_);
                    v___x_5519_ = lean_box(0);
                    if v_isShared_5489_ == 0 {
                        lean_ctor_set(v___x_5488_, 0, v___x_5519_);
                        v___x_5521_ = v___x_5488_;
                        state = 53;
                        continue;
                    } else {
                        v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5519_);
                        v___x_5521_ = v_reuseFailAlloc_5522_;
                        state = 53;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5488_);
                    v_val_5523_ = lean_ctor_get(v_a_5500_, 0);
                    lean_inc(v_val_5523_);
                    lean_dec_ref_known(v_a_5500_, 1);
                    lean_inc(v_val_5498_);
                    v___x_5524_ = l_Lean_Name_num___override(v_val_5523_, v_val_5498_);
                    if lean_obj_tag(v___x_5524_) == 0 {
                        v___x_5525_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2__spec__1___redArg___closed__0);
                        v___y_5505_ = v___x_5525_;
                        state = 50;
                        continue;
                    } else {
                        v_hash_5526_ = lean_ctor_get_uint64(
                            v___x_5524_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        lean_dec(v___x_5524_);
                        v___y_5505_ = v_hash_5526_;
                        state = 50;
                        continue;
                    }
                }
            }
            50 => {
                v___x_5506_ = lean_unsigned_to_nat(2);
                v___x_5507_ = lean_mk_empty_array_with_capacity(v___x_5506_);
                v___x_5508_ = lean_array_push(v___x_5507_, v_val_5482_);
                v___x_5509_ = lean_array_push(v___x_5508_, v_val_5494_);
                v___x_5510_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__3;
                v___x_5511_ = l_Lean_Compiler_LCNF_uint64ToByteArrayLE(v___y_5505_);
                v___x_5512_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_5512_, 0, v___x_5506_);
                lean_ctor_set(v___x_5512_, 1, v___x_5509_);
                lean_ctor_set(v___x_5512_, 2, v___x_5510_);
                lean_ctor_set(v___x_5512_, 3, v___x_5511_);
                if v_isShared_5497_ == 0 {
                    lean_ctor_set(v___x_5496_, 0, v___x_5512_);
                    v___x_5514_ = v___x_5496_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5512_);
                    v___x_5514_ = v_reuseFailAlloc_5518_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                if v_isShared_5503_ == 0 {
                    lean_ctor_set(v___x_5502_, 0, v___x_5514_);
                    v___x_5516_ = v___x_5502_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5514_);
                    v___x_5516_ = v_reuseFailAlloc_5517_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5516_;
            }
            53 => {
                return v___x_5521_;
            }
            54 => {
                if v_isShared_5531_ == 0 {
                    v___x_5533_ = v___x_5530_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_5534_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_a_5528_);
                    v___x_5533_ = v_reuseFailAlloc_5534_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_5533_;
            }
            56 => {
                return v___x_5538_;
            }
            57 => {
                v___x_5620_ = lean_st_ref_get(v_a_5185_);
                v___x_5626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_5620_, v_fvarId_5616_);
                lean_dec(v_fvarId_5616_);
                lean_dec(v___x_5620_);
                match lean_obj_tag(v___x_5626_) {
                    6 => {
                        v_elems_5627_ = lean_ctor_get(v___x_5626_, 0);
                        lean_inc(v_elems_5627_);
                        v_remainingCapacity_5628_ = lean_ctor_get(v___x_5626_, 1);
                        lean_inc(v_remainingCapacity_5628_);
                        lean_dec_ref_known(v___x_5626_, 2);
                        v___x_5629_ = lean_nat_dec_eq(v_remainingCapacity_5628_, v___x_5614_);
                        lean_dec(v_remainingCapacity_5628_);
                        if v___x_5629_ == 0 {
                            lean_dec(v_elems_5627_);
                            state = 58;
                            continue;
                        } else {
                            lean_del_object(v___x_5618_);
                            v___x_5630_ = lean_box(0);
                            v___x_5631_ = l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1___redArg(v_elems_5627_, v___x_5630_);
                            v_a_5632_ = lean_ctor_get(v___x_5631_, 0);
                            v_isSharedCheck_5654_ = (!lean_is_exclusive(v___x_5631_)) as u8;
                            if v_isSharedCheck_5654_ == 0 {
                                v___x_5634_ = v___x_5631_;
                                v_isShared_5635_ = v_isSharedCheck_5654_;
                                state = 60;
                                continue;
                            } else {
                                lean_inc(v_a_5632_);
                                lean_dec(v___x_5631_);
                                v___x_5634_ = lean_box(0);
                                v_isShared_5635_ = v_isSharedCheck_5654_;
                                state = 60;
                                continue;
                            }
                        }
                    }
                    0 => {
                        v_arg_5655_ = lean_ctor_get(v___x_5626_, 0);
                        lean_inc_ref(v_arg_5655_);
                        lean_dec_ref_known(v___x_5626_, 1);
                        if lean_obj_tag(v_arg_5655_) == 1 {
                            lean_del_object(v___x_5618_);
                            v_n_5656_ = lean_ctor_get(v_arg_5655_, 0);
                            lean_inc(v_n_5656_);
                            lean_dec_ref_known(v_arg_5655_, 1);
                            v___x_5657_ = lean_st_ref_get(v_a_5189_);
                            v_env_5658_ = lean_ctor_get(v___x_5657_, 0);
                            lean_inc_ref(v_env_5658_);
                            lean_dec(v___x_5657_);
                            v___x_5659_ = l_Lean_Compiler_LCNF_getSimpleGroundExprWithResolvedRefs(
                                v_env_5658_,
                                v_n_5656_,
                            );
                            if lean_obj_tag(v___x_5659_) == 1 {
                                v_val_5660_ = lean_ctor_get(v___x_5659_, 0);
                                lean_inc(v_val_5660_);
                                lean_dec_ref_known(v___x_5659_, 1);
                                if lean_obj_tag(v_val_5660_) == 5 {
                                    v_elems_5661_ = lean_ctor_get(v_val_5660_, 0);
                                    v_isSharedCheck_5699_ = (!lean_is_exclusive(v_val_5660_)) as u8;
                                    if v_isSharedCheck_5699_ == 0 {
                                        v___x_5663_ = v_val_5660_;
                                        v_isShared_5664_ = v_isSharedCheck_5699_;
                                        state = 65;
                                        continue;
                                    } else {
                                        lean_inc(v_elems_5661_);
                                        lean_dec(v_val_5660_);
                                        v___x_5663_ = lean_box(0);
                                        v_isShared_5664_ = v_isSharedCheck_5699_;
                                        state = 65;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_val_5660_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_5659_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_arg_5655_);
                            state = 58;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec_ref(v___x_5626_);
                        state = 58;
                        continue;
                    }
                }
            }
            58 => {
                v___x_5622_ = lean_box(0);
                if v_isShared_5619_ == 0 {
                    lean_ctor_set_tag(v___x_5618_, 0);
                    lean_ctor_set(v___x_5618_, 0, v___x_5622_);
                    v___x_5624_ = v___x_5618_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_5625_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5625_, 0, v___x_5622_);
                    v___x_5624_ = v_reuseFailAlloc_5625_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5624_;
            }
            60 => {
                if lean_obj_tag(v_a_5632_) == 0 {
                    v___x_5636_ = lean_box(0);
                    if v_isShared_5635_ == 0 {
                        lean_ctor_set(v___x_5634_, 0, v___x_5636_);
                        v___x_5638_ = v___x_5634_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5636_);
                        v___x_5638_ = v_reuseFailAlloc_5639_;
                        state = 61;
                        continue;
                    }
                } else {
                    v_val_5640_ = lean_ctor_get(v_a_5632_, 0);
                    v_isSharedCheck_5653_ = (!lean_is_exclusive(v_a_5632_)) as u8;
                    if v_isSharedCheck_5653_ == 0 {
                        v___x_5642_ = v_a_5632_;
                        v_isShared_5643_ = v_isSharedCheck_5653_;
                        state = 62;
                        continue;
                    } else {
                        lean_inc(v_val_5640_);
                        lean_dec(v_a_5632_);
                        v___x_5642_ = lean_box(0);
                        v_isShared_5643_ = v_isSharedCheck_5653_;
                        state = 62;
                        continue;
                    }
                }
            }
            61 => {
                return v___x_5638_;
            }
            62 => {
                v___x_5644_ = lean_array_mk(v_val_5640_);
                v___x_5645_ = l_Array_reverse___redArg(v___x_5644_);
                v___x_5646_ = lean_alloc_ctor(6, 1, (0) as u32);
                lean_ctor_set(v___x_5646_, 0, v___x_5645_);
                if v_isShared_5643_ == 0 {
                    lean_ctor_set(v___x_5642_, 0, v___x_5646_);
                    v___x_5648_ = v___x_5642_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_5652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5652_, 0, v___x_5646_);
                    v___x_5648_ = v_reuseFailAlloc_5652_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_5635_ == 0 {
                    lean_ctor_set(v___x_5634_, 0, v___x_5648_);
                    v___x_5650_ = v___x_5634_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
                    v___x_5650_ = v_reuseFailAlloc_5651_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_5650_;
            }
            65 => {
                v_sz_5665_ = lean_array_size(v_elems_5661_);
                v___x_5666_ = 0usize;
                v___x_5667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2___redArg(v_sz_5665_, v___x_5666_, v_elems_5661_);
                if lean_obj_tag(v___x_5667_) == 0 {
                    v_a_5668_ = lean_ctor_get(v___x_5667_, 0);
                    v_isSharedCheck_5690_ = (!lean_is_exclusive(v___x_5667_)) as u8;
                    if v_isSharedCheck_5690_ == 0 {
                        v___x_5670_ = v___x_5667_;
                        v_isShared_5671_ = v_isSharedCheck_5690_;
                        state = 66;
                        continue;
                    } else {
                        lean_inc(v_a_5668_);
                        lean_dec(v___x_5667_);
                        v___x_5670_ = lean_box(0);
                        v_isShared_5671_ = v_isSharedCheck_5690_;
                        state = 66;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5663_);
                    v_a_5691_ = lean_ctor_get(v___x_5667_, 0);
                    v_isSharedCheck_5698_ = (!lean_is_exclusive(v___x_5667_)) as u8;
                    if v_isSharedCheck_5698_ == 0 {
                        v___x_5693_ = v___x_5667_;
                        v_isShared_5694_ = v_isSharedCheck_5698_;
                        state = 72;
                        continue;
                    } else {
                        lean_inc(v_a_5691_);
                        lean_dec(v___x_5667_);
                        v___x_5693_ = lean_box(0);
                        v_isShared_5694_ = v_isSharedCheck_5698_;
                        state = 72;
                        continue;
                    }
                }
            }
            66 => {
                if lean_obj_tag(v_a_5668_) == 0 {
                    lean_del_object(v___x_5663_);
                    v___x_5672_ = lean_box(0);
                    if v_isShared_5671_ == 0 {
                        lean_ctor_set(v___x_5670_, 0, v___x_5672_);
                        v___x_5674_ = v___x_5670_;
                        state = 67;
                        continue;
                    } else {
                        v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5675_, 0, v___x_5672_);
                        v___x_5674_ = v_reuseFailAlloc_5675_;
                        state = 67;
                        continue;
                    }
                } else {
                    v_val_5676_ = lean_ctor_get(v_a_5668_, 0);
                    v_isSharedCheck_5689_ = (!lean_is_exclusive(v_a_5668_)) as u8;
                    if v_isSharedCheck_5689_ == 0 {
                        v___x_5678_ = v_a_5668_;
                        v_isShared_5679_ = v_isSharedCheck_5689_;
                        state = 68;
                        continue;
                    } else {
                        lean_inc(v_val_5676_);
                        lean_dec(v_a_5668_);
                        v___x_5678_ = lean_box(0);
                        v_isShared_5679_ = v_isSharedCheck_5689_;
                        state = 68;
                        continue;
                    }
                }
            }
            67 => {
                return v___x_5674_;
            }
            68 => {
                if v_isShared_5664_ == 0 {
                    lean_ctor_set_tag(v___x_5663_, 6);
                    lean_ctor_set(v___x_5663_, 0, v_val_5676_);
                    v___x_5681_ = v___x_5663_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_5688_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_val_5676_);
                    v___x_5681_ = v_reuseFailAlloc_5688_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_5679_ == 0 {
                    lean_ctor_set(v___x_5678_, 0, v___x_5681_);
                    v___x_5683_ = v___x_5678_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5681_);
                    v___x_5683_ = v_reuseFailAlloc_5687_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_5671_ == 0 {
                    lean_ctor_set(v___x_5670_, 0, v___x_5683_);
                    v___x_5685_ = v___x_5670_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 0, v___x_5683_);
                    v___x_5685_ = v_reuseFailAlloc_5686_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_5685_;
            }
            72 => {
                if v_isShared_5694_ == 0 {
                    v___x_5696_ = v___x_5693_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_5697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_a_5691_);
                    v___x_5696_ = v_reuseFailAlloc_5697_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_5696_;
            }
            74 => {
                v___x_5727_ = lean_unsigned_to_nat(2);
                v___x_5728_ = lean_array_fget(v_args_5590_, v___x_5727_);
                lean_dec_ref(v_args_5590_);
                if lean_obj_tag(v___x_5728_) == 1 {
                    v_fvarId_5729_ = lean_ctor_get(v___x_5728_, 0);
                    v_isSharedCheck_5775_ = (!lean_is_exclusive(v___x_5728_)) as u8;
                    if v_isSharedCheck_5775_ == 0 {
                        v___x_5731_ = v___x_5728_;
                        v_isShared_5732_ = v_isSharedCheck_5775_;
                        state = 75;
                        continue;
                    } else {
                        lean_inc(v_fvarId_5729_);
                        lean_dec(v___x_5728_);
                        v___x_5731_ = lean_box(0);
                        v_isShared_5732_ = v_isSharedCheck_5775_;
                        state = 75;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5728_);
                    lean_del_object(v___x_5725_);
                    lean_dec(v_fvarId_5723_);
                    state = 11;
                    continue;
                }
            }
            75 => {
                v___x_5733_ = lean_st_ref_get(v_a_5185_);
                v___x_5734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_5733_, v_fvarId_5723_);
                lean_dec(v_fvarId_5723_);
                lean_dec(v___x_5733_);
                if lean_obj_tag(v___x_5734_) == 6 {
                    v_elems_5735_ = lean_ctor_get(v___x_5734_, 0);
                    v_remainingCapacity_5736_ = lean_ctor_get(v___x_5734_, 1);
                    v_isSharedCheck_5770_ = (!lean_is_exclusive(v___x_5734_)) as u8;
                    if v_isSharedCheck_5770_ == 0 {
                        v___x_5738_ = v___x_5734_;
                        v_isShared_5739_ = v_isSharedCheck_5770_;
                        state = 76;
                        continue;
                    } else {
                        lean_inc(v_remainingCapacity_5736_);
                        lean_inc(v_elems_5735_);
                        lean_dec(v___x_5734_);
                        v___x_5738_ = lean_box(0);
                        v_isShared_5739_ = v_isSharedCheck_5770_;
                        state = 76;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_5734_);
                    lean_dec(v_fvarId_5729_);
                    lean_del_object(v___x_5725_);
                    v___x_5771_ = lean_box(0);
                    if v_isShared_5732_ == 0 {
                        lean_ctor_set_tag(v___x_5731_, 0);
                        lean_ctor_set(v___x_5731_, 0, v___x_5771_);
                        v___x_5773_ = v___x_5731_;
                        state = 84;
                        continue;
                    } else {
                        v_reuseFailAlloc_5774_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5774_, 0, v___x_5771_);
                        v___x_5773_ = v_reuseFailAlloc_5774_;
                        state = 84;
                        continue;
                    }
                }
            }
            76 => {
                v___x_5740_ = lean_nat_dec_lt(v___x_5721_, v_remainingCapacity_5736_);
                lean_dec(v_remainingCapacity_5736_);
                if v___x_5740_ == 0 {
                    v___x_5741_ = lean_st_ref_get(v_a_5185_);
                    v___x_5742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_5741_, v_fvarId_5729_);
                    lean_dec(v_fvarId_5729_);
                    lean_dec(v___x_5741_);
                    if lean_obj_tag(v___x_5742_) == 0 {
                        v_arg_5743_ = lean_ctor_get(v___x_5742_, 0);
                        v_isSharedCheck_5761_ = (!lean_is_exclusive(v___x_5742_)) as u8;
                        if v_isSharedCheck_5761_ == 0 {
                            v___x_5745_ = v___x_5742_;
                            v_isShared_5746_ = v_isSharedCheck_5761_;
                            state = 77;
                            continue;
                        } else {
                            lean_inc(v_arg_5743_);
                            lean_dec(v___x_5742_);
                            v___x_5745_ = lean_box(0);
                            v_isShared_5746_ = v_isSharedCheck_5761_;
                            state = 77;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_5742_);
                        lean_del_object(v___x_5738_);
                        lean_dec(v_elems_5735_);
                        lean_del_object(v___x_5725_);
                        v___x_5762_ = lean_box(0);
                        if v_isShared_5732_ == 0 {
                            lean_ctor_set_tag(v___x_5731_, 0);
                            lean_ctor_set(v___x_5731_, 0, v___x_5762_);
                            v___x_5764_ = v___x_5731_;
                            state = 82;
                            continue;
                        } else {
                            v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5765_, 0, v___x_5762_);
                            v___x_5764_ = v_reuseFailAlloc_5765_;
                            state = 82;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5738_);
                    lean_dec(v_elems_5735_);
                    lean_dec(v_fvarId_5729_);
                    lean_del_object(v___x_5725_);
                    v___x_5766_ = lean_box(0);
                    if v_isShared_5732_ == 0 {
                        lean_ctor_set_tag(v___x_5731_, 0);
                        lean_ctor_set(v___x_5731_, 0, v___x_5766_);
                        v___x_5768_ = v___x_5731_;
                        state = 83;
                        continue;
                    } else {
                        v_reuseFailAlloc_5769_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5769_, 0, v___x_5766_);
                        v___x_5768_ = v_reuseFailAlloc_5769_;
                        state = 83;
                        continue;
                    }
                }
            }
            77 => {
                if v_isShared_5739_ == 0 {
                    lean_ctor_set_tag(v___x_5738_, 1);
                    lean_ctor_set(v___x_5738_, 1, v_elems_5735_);
                    lean_ctor_set(v___x_5738_, 0, v_arg_5743_);
                    v___x_5748_ = v___x_5738_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_5760_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5760_, 0, v_arg_5743_);
                    lean_ctor_set(v_reuseFailAlloc_5760_, 1, v_elems_5735_);
                    v___x_5748_ = v_reuseFailAlloc_5760_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                v___x_5749_ = lean_array_mk(v___x_5748_);
                v___x_5750_ = l_Array_reverse___redArg(v___x_5749_);
                if v_isShared_5746_ == 0 {
                    lean_ctor_set_tag(v___x_5745_, 5);
                    lean_ctor_set(v___x_5745_, 0, v___x_5750_);
                    v___x_5752_ = v___x_5745_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5759_, 0, v___x_5750_);
                    v___x_5752_ = v_reuseFailAlloc_5759_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                if v_isShared_5732_ == 0 {
                    lean_ctor_set(v___x_5731_, 0, v___x_5752_);
                    v___x_5754_ = v___x_5731_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5758_, 0, v___x_5752_);
                    v___x_5754_ = v_reuseFailAlloc_5758_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                if v_isShared_5726_ == 0 {
                    lean_ctor_set_tag(v___x_5725_, 0);
                    lean_ctor_set(v___x_5725_, 0, v___x_5754_);
                    v___x_5756_ = v___x_5725_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_5757_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5754_);
                    v___x_5756_ = v_reuseFailAlloc_5757_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_5756_;
            }
            82 => {
                return v___x_5764_;
            }
            83 => {
                return v___x_5768_;
            }
            84 => {
                return v___x_5773_;
            }
            85 => {
                v___x_5846_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs(v_args_5842_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_);
                if lean_obj_tag(v___x_5846_) == 0 {
                    v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
                    v_isSharedCheck_5869_ = (!lean_is_exclusive(v___x_5846_)) as u8;
                    if v_isSharedCheck_5869_ == 0 {
                        v___x_5849_ = v___x_5846_;
                        v_isShared_5850_ = v_isSharedCheck_5869_;
                        state = 86;
                        continue;
                    } else {
                        lean_inc(v_a_5847_);
                        lean_dec(v___x_5846_);
                        v___x_5849_ = lean_box(0);
                        v_isShared_5850_ = v_isSharedCheck_5869_;
                        state = 86;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5844_);
                    lean_dec(v_fn_5841_);
                    v_a_5870_ = lean_ctor_get(v___x_5846_, 0);
                    v_isSharedCheck_5877_ = (!lean_is_exclusive(v___x_5846_)) as u8;
                    if v_isSharedCheck_5877_ == 0 {
                        v___x_5872_ = v___x_5846_;
                        v_isShared_5873_ = v_isSharedCheck_5877_;
                        state = 92;
                        continue;
                    } else {
                        lean_inc(v_a_5870_);
                        lean_dec(v___x_5846_);
                        v___x_5872_ = lean_box(0);
                        v_isShared_5873_ = v_isSharedCheck_5877_;
                        state = 92;
                        continue;
                    }
                }
            }
            86 => {
                if lean_obj_tag(v_a_5847_) == 0 {
                    lean_del_object(v___x_5844_);
                    lean_dec(v_fn_5841_);
                    v___x_5851_ = lean_box(0);
                    if v_isShared_5850_ == 0 {
                        lean_ctor_set(v___x_5849_, 0, v___x_5851_);
                        v___x_5853_ = v___x_5849_;
                        state = 87;
                        continue;
                    } else {
                        v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5854_, 0, v___x_5851_);
                        v___x_5853_ = v_reuseFailAlloc_5854_;
                        state = 87;
                        continue;
                    }
                } else {
                    v_val_5855_ = lean_ctor_get(v_a_5847_, 0);
                    v_isSharedCheck_5868_ = (!lean_is_exclusive(v_a_5847_)) as u8;
                    if v_isSharedCheck_5868_ == 0 {
                        v___x_5857_ = v_a_5847_;
                        v_isShared_5858_ = v_isSharedCheck_5868_;
                        state = 88;
                        continue;
                    } else {
                        lean_inc(v_val_5855_);
                        lean_dec(v_a_5847_);
                        v___x_5857_ = lean_box(0);
                        v_isShared_5858_ = v_isSharedCheck_5868_;
                        state = 88;
                        continue;
                    }
                }
            }
            87 => {
                return v___x_5853_;
            }
            88 => {
                if v_isShared_5845_ == 0 {
                    lean_ctor_set_tag(v___x_5844_, 2);
                    lean_ctor_set(v___x_5844_, 1, v_val_5855_);
                    v___x_5860_ = v___x_5844_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_5867_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_fn_5841_);
                    lean_ctor_set(v_reuseFailAlloc_5867_, 1, v_val_5855_);
                    v___x_5860_ = v_reuseFailAlloc_5867_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_5858_ == 0 {
                    lean_ctor_set(v___x_5857_, 0, v___x_5860_);
                    v___x_5862_ = v___x_5857_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_5866_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___x_5860_);
                    v___x_5862_ = v_reuseFailAlloc_5866_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_5850_ == 0 {
                    lean_ctor_set(v___x_5849_, 0, v___x_5862_);
                    v___x_5864_ = v___x_5849_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_5865_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5865_, 0, v___x_5862_);
                    v___x_5864_ = v_reuseFailAlloc_5865_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_5864_;
            }
            92 => {
                if v_isShared_5873_ == 0 {
                    v___x_5875_ = v___x_5872_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
                    v___x_5875_ = v_reuseFailAlloc_5876_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                return v___x_5875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___boxed(
    mut v_e_5879_: *mut LeanObject,
    mut v_a_5880_: *mut LeanObject,
    mut v_a_5881_: *mut LeanObject,
    mut v_a_5882_: *mut LeanObject,
    mut v_a_5883_: *mut LeanObject,
    mut v_a_5884_: *mut LeanObject,
    mut v_a_5885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5886_: *mut LeanObject = core::ptr::null_mut();
    v_res_5886_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet(v_e_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_);
    lean_dec(v_a_5884_);
    lean_dec_ref(v_a_5883_);
    lean_dec(v_a_5882_);
    lean_dec_ref(v_a_5881_);
    lean_dec(v_a_5880_);
    return v_res_5886_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0(
    mut v_as_5887_: *mut LeanObject,
    mut v_sz_5888_: usize,
    mut v_i_5889_: usize,
    mut v_b_5890_: *mut LeanObject,
    mut v___y_5891_: *mut LeanObject,
    mut v___y_5892_: *mut LeanObject,
    mut v___y_5893_: *mut LeanObject,
    mut v___y_5894_: *mut LeanObject,
    mut v___y_5895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    v___x_5897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0___redArg(v_as_5887_, v_sz_5888_, v_i_5889_, v_b_5890_, v___y_5891_, v___y_5895_);
    return v___x_5897_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0___boxed(
    mut v_as_5898_: *mut LeanObject,
    mut v_sz_5899_: *mut LeanObject,
    mut v_i_5900_: *mut LeanObject,
    mut v_b_5901_: *mut LeanObject,
    mut v___y_5902_: *mut LeanObject,
    mut v___y_5903_: *mut LeanObject,
    mut v___y_5904_: *mut LeanObject,
    mut v___y_5905_: *mut LeanObject,
    mut v___y_5906_: *mut LeanObject,
    mut v___y_5907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5908_: usize = 0;
    let mut v_i_boxed_5909_: usize = 0;
    let mut v_res_5910_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5908_ = lean_unbox_usize(v_sz_5899_);
    lean_dec(v_sz_5899_);
    v_i_boxed_5909_ = lean_unbox_usize(v_i_5900_);
    lean_dec(v_i_5900_);
    v_res_5910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__0(v_as_5898_, v_sz_boxed_5908_, v_i_boxed_5909_, v_b_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
    lean_dec(v___y_5906_);
    lean_dec_ref(v___y_5905_);
    lean_dec(v___y_5904_);
    lean_dec_ref(v___y_5903_);
    lean_dec(v___y_5902_);
    lean_dec_ref(v_as_5898_);
    return v_res_5910_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1(
    mut v_x_5911_: *mut LeanObject,
    mut v_x_5912_: *mut LeanObject,
    mut v___y_5913_: *mut LeanObject,
    mut v___y_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
    mut v___y_5916_: *mut LeanObject,
    mut v___y_5917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    v___x_5919_ = l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1___redArg(v_x_5911_, v_x_5912_);
    return v___x_5919_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1___boxed(
    mut v_x_5920_: *mut LeanObject,
    mut v_x_5921_: *mut LeanObject,
    mut v___y_5922_: *mut LeanObject,
    mut v___y_5923_: *mut LeanObject,
    mut v___y_5924_: *mut LeanObject,
    mut v___y_5925_: *mut LeanObject,
    mut v___y_5926_: *mut LeanObject,
    mut v___y_5927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5928_: *mut LeanObject = core::ptr::null_mut();
    v_res_5928_ = l_List_mapM_loop___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__1(v_x_5920_, v_x_5921_, v___y_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
    lean_dec(v___y_5926_);
    lean_dec_ref(v___y_5925_);
    lean_dec(v___y_5924_);
    lean_dec_ref(v___y_5923_);
    lean_dec(v___y_5922_);
    return v_res_5928_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2(
    mut v_sz_5929_: usize,
    mut v_i_5930_: usize,
    mut v_bs_5931_: *mut LeanObject,
    mut v___y_5932_: *mut LeanObject,
    mut v___y_5933_: *mut LeanObject,
    mut v___y_5934_: *mut LeanObject,
    mut v___y_5935_: *mut LeanObject,
    mut v___y_5936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    v___x_5938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2___redArg(v_sz_5929_, v_i_5930_, v_bs_5931_);
    return v___x_5938_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2___boxed(
    mut v_sz_5939_: *mut LeanObject,
    mut v_i_5940_: *mut LeanObject,
    mut v_bs_5941_: *mut LeanObject,
    mut v___y_5942_: *mut LeanObject,
    mut v___y_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
    mut v___y_5945_: *mut LeanObject,
    mut v___y_5946_: *mut LeanObject,
    mut v___y_5947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5948_: usize = 0;
    let mut v_i_boxed_5949_: usize = 0;
    let mut v_res_5950_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5948_ = lean_unbox_usize(v_sz_5939_);
    lean_dec(v_sz_5939_);
    v_i_boxed_5949_ = lean_unbox_usize(v_i_5940_);
    lean_dec(v_i_5940_);
    v_res_5950_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet_spec__2(v_sz_boxed_5948_, v_i_boxed_5949_, v_bs_5941_, v___y_5942_, v___y_5943_, v___y_5944_, v___y_5945_, v___y_5946_);
    lean_dec(v___y_5946_);
    lean_dec_ref(v___y_5945_);
    lean_dec(v___y_5944_);
    lean_dec_ref(v___y_5943_);
    lean_dec(v___y_5942_);
    return v_res_5950_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_5951_: *mut LeanObject,
    mut v_x_5952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: u64 = 0;
    let mut v___x_5961_: u64 = 0;
    let mut v___x_5962_: u64 = 0;
    let mut v_fold_5963_: u64 = 0;
    let mut v___x_5964_: u64 = 0;
    let mut v___x_5965_: u64 = 0;
    let mut v___x_5966_: u64 = 0;
    let mut v___x_5967_: usize = 0;
    let mut v___x_5968_: usize = 0;
    let mut v___x_5969_: usize = 0;
    let mut v___x_5970_: usize = 0;
    let mut v___x_5971_: usize = 0;
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5952_) == 0 {
                    return v_x_5951_;
                } else {
                    v_key_5953_ = lean_ctor_get(v_x_5952_, 0);
                    v_value_5954_ = lean_ctor_get(v_x_5952_, 1);
                    v_tail_5955_ = lean_ctor_get(v_x_5952_, 2);
                    v_isSharedCheck_5978_ = (!lean_is_exclusive(v_x_5952_)) as u8;
                    if v_isSharedCheck_5978_ == 0 {
                        v___x_5957_ = v_x_5952_;
                        v_isShared_5958_ = v_isSharedCheck_5978_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5955_);
                        lean_inc(v_value_5954_);
                        lean_inc(v_key_5953_);
                        lean_dec(v_x_5952_);
                        v___x_5957_ = lean_box(0);
                        v_isShared_5958_ = v_isSharedCheck_5978_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5959_ = lean_array_get_size(v_x_5951_);
                v___x_5960_ = l_Lean_instHashableFVarId_hash(v_key_5953_);
                v___x_5961_ = 32u64;
                v___x_5962_ = lean_uint64_shift_right(v___x_5960_, v___x_5961_);
                v_fold_5963_ = lean_uint64_xor(v___x_5960_, v___x_5962_);
                v___x_5964_ = 16u64;
                v___x_5965_ = lean_uint64_shift_right(v_fold_5963_, v___x_5964_);
                v___x_5966_ = lean_uint64_xor(v_fold_5963_, v___x_5965_);
                v___x_5967_ = lean_uint64_to_usize(v___x_5966_);
                v___x_5968_ = lean_usize_of_nat(v___x_5959_);
                v___x_5969_ = 1usize;
                v___x_5970_ = lean_usize_sub(v___x_5968_, v___x_5969_);
                v___x_5971_ = lean_usize_land(v___x_5967_, v___x_5970_);
                v___x_5972_ = lean_array_uget_borrowed(v_x_5951_, v___x_5971_);
                lean_inc(v___x_5972_);
                if v_isShared_5958_ == 0 {
                    lean_ctor_set(v___x_5957_, 2, v___x_5972_);
                    v___x_5974_ = v___x_5957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5977_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_key_5953_);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_value_5954_);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 2, v___x_5972_);
                    v___x_5974_ = v_reuseFailAlloc_5977_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5975_ = lean_array_uset(v_x_5951_, v___x_5971_, v___x_5974_);
                v_x_5951_ = v___x_5975_;
                v_x_5952_ = v_tail_5955_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3___redArg(
    mut v_i_5979_: *mut LeanObject,
    mut v_source_5980_: *mut LeanObject,
    mut v_target_5981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: u8 = 0;
    let mut v_es_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5982_ = lean_array_get_size(v_source_5980_);
                v___x_5983_ = lean_nat_dec_lt(v_i_5979_, v___x_5982_);
                if v___x_5983_ == 0 {
                    lean_dec_ref(v_source_5980_);
                    lean_dec(v_i_5979_);
                    return v_target_5981_;
                } else {
                    v_es_5984_ = lean_array_fget(v_source_5980_, v_i_5979_);
                    v___x_5985_ = lean_box(0);
                    v_source_5986_ = lean_array_fset(v_source_5980_, v_i_5979_, v___x_5985_);
                    v_target_5987_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3_spec__4___redArg(v_target_5981_, v_es_5984_);
                    v___x_5988_ = lean_unsigned_to_nat(1);
                    v___x_5989_ = lean_nat_add(v_i_5979_, v___x_5988_);
                    lean_dec(v_i_5979_);
                    v_i_5979_ = v___x_5989_;
                    v_source_5980_ = v_source_5986_;
                    v_target_5981_ = v_target_5987_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2___redArg(
    mut v_data_5991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    v___x_5992_ = lean_array_get_size(v_data_5991_);
    v___x_5993_ = lean_unsigned_to_nat(2);
    v_nbuckets_5994_ = lean_nat_mul(v___x_5992_, v___x_5993_);
    v___x_5995_ = lean_unsigned_to_nat(0);
    v___x_5996_ = lean_box(0);
    v___x_5997_ = lean_mk_array(v_nbuckets_5994_, v___x_5996_);
    v___x_5998_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3___redArg(v___x_5995_, v_data_5991_, v___x_5997_);
    return v___x_5998_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1___redArg(
    mut v_a_5999_: *mut LeanObject,
    mut v_x_6000_: *mut LeanObject,
) -> u8 {
    let mut v___x_6001_: u8 = 0;
    let mut v_key_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6000_) == 0 {
                    v___x_6001_ = 0;
                    return v___x_6001_;
                } else {
                    v_key_6002_ = lean_ctor_get(v_x_6000_, 0);
                    v_tail_6003_ = lean_ctor_get(v_x_6000_, 2);
                    v___x_6004_ = l_Lean_instBEqFVarId_beq(v_key_6002_, v_a_5999_);
                    if v___x_6004_ == 0 {
                        v_x_6000_ = v_tail_6003_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6004_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1___redArg___boxed(
    mut v_a_6006_: *mut LeanObject,
    mut v_x_6007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6008_: u8 = 0;
    let mut v_r_6009_: *mut LeanObject = core::ptr::null_mut();
    v_res_6008_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1___redArg(v_a_6006_, v_x_6007_);
    lean_dec(v_x_6007_);
    lean_dec(v_a_6006_);
    v_r_6009_ = lean_box((v_res_6008_) as usize);
    return v_r_6009_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__3___redArg(
    mut v_a_6010_: *mut LeanObject,
    mut v_b_6011_: *mut LeanObject,
    mut v_x_6012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6018_: u8 = 0;
    let mut v___x_6019_: u8 = 0;
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6012_) == 0 {
                    lean_dec(v_b_6011_);
                    lean_dec(v_a_6010_);
                    return v_x_6012_;
                } else {
                    v_key_6013_ = lean_ctor_get(v_x_6012_, 0);
                    v_value_6014_ = lean_ctor_get(v_x_6012_, 1);
                    v_tail_6015_ = lean_ctor_get(v_x_6012_, 2);
                    v_isSharedCheck_6027_ = (!lean_is_exclusive(v_x_6012_)) as u8;
                    if v_isSharedCheck_6027_ == 0 {
                        v___x_6017_ = v_x_6012_;
                        v_isShared_6018_ = v_isSharedCheck_6027_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6015_);
                        lean_inc(v_value_6014_);
                        lean_inc(v_key_6013_);
                        lean_dec(v_x_6012_);
                        v___x_6017_ = lean_box(0);
                        v_isShared_6018_ = v_isSharedCheck_6027_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6019_ = l_Lean_instBEqFVarId_beq(v_key_6013_, v_a_6010_);
                if v___x_6019_ == 0 {
                    v___x_6020_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__3___redArg(v_a_6010_, v_b_6011_, v_tail_6015_);
                    if v_isShared_6018_ == 0 {
                        lean_ctor_set(v___x_6017_, 2, v___x_6020_);
                        v___x_6022_ = v___x_6017_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6023_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_key_6013_);
                        lean_ctor_set(v_reuseFailAlloc_6023_, 1, v_value_6014_);
                        lean_ctor_set(v_reuseFailAlloc_6023_, 2, v___x_6020_);
                        v___x_6022_ = v_reuseFailAlloc_6023_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_6014_);
                    lean_dec(v_key_6013_);
                    if v_isShared_6018_ == 0 {
                        lean_ctor_set(v___x_6017_, 1, v_b_6011_);
                        lean_ctor_set(v___x_6017_, 0, v_a_6010_);
                        v___x_6025_ = v___x_6017_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6026_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_a_6010_);
                        lean_ctor_set(v_reuseFailAlloc_6026_, 1, v_b_6011_);
                        lean_ctor_set(v_reuseFailAlloc_6026_, 2, v_tail_6015_);
                        v___x_6025_ = v_reuseFailAlloc_6026_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6022_;
            }
            3 => {
                return v___x_6025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(
    mut v_m_6028_: *mut LeanObject,
    mut v_a_6029_: *mut LeanObject,
    mut v_b_6030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6035_: u8 = 0;
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: u64 = 0;
    let mut v___x_6038_: u64 = 0;
    let mut v___x_6039_: u64 = 0;
    let mut v_fold_6040_: u64 = 0;
    let mut v___x_6041_: u64 = 0;
    let mut v___x_6042_: u64 = 0;
    let mut v___x_6043_: u64 = 0;
    let mut v___x_6044_: usize = 0;
    let mut v___x_6045_: usize = 0;
    let mut v___x_6046_: usize = 0;
    let mut v___x_6047_: usize = 0;
    let mut v___x_6048_: usize = 0;
    let mut v_bkt_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: u8 = 0;
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: u8 = 0;
    let mut v_val_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6031_ = lean_ctor_get(v_m_6028_, 0);
                v_buckets_6032_ = lean_ctor_get(v_m_6028_, 1);
                v_isSharedCheck_6075_ = (!lean_is_exclusive(v_m_6028_)) as u8;
                if v_isSharedCheck_6075_ == 0 {
                    v___x_6034_ = v_m_6028_;
                    v_isShared_6035_ = v_isSharedCheck_6075_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_6032_);
                    lean_inc(v_size_6031_);
                    lean_dec(v_m_6028_);
                    v___x_6034_ = lean_box(0);
                    v_isShared_6035_ = v_isSharedCheck_6075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6036_ = lean_array_get_size(v_buckets_6032_);
                v___x_6037_ = l_Lean_instHashableFVarId_hash(v_a_6029_);
                v___x_6038_ = 32u64;
                v___x_6039_ = lean_uint64_shift_right(v___x_6037_, v___x_6038_);
                v_fold_6040_ = lean_uint64_xor(v___x_6037_, v___x_6039_);
                v___x_6041_ = 16u64;
                v___x_6042_ = lean_uint64_shift_right(v_fold_6040_, v___x_6041_);
                v___x_6043_ = lean_uint64_xor(v_fold_6040_, v___x_6042_);
                v___x_6044_ = lean_uint64_to_usize(v___x_6043_);
                v___x_6045_ = lean_usize_of_nat(v___x_6036_);
                v___x_6046_ = 1usize;
                v___x_6047_ = lean_usize_sub(v___x_6045_, v___x_6046_);
                v___x_6048_ = lean_usize_land(v___x_6044_, v___x_6047_);
                v_bkt_6049_ = lean_array_uget_borrowed(v_buckets_6032_, v___x_6048_);
                v___x_6050_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1___redArg(v_a_6029_, v_bkt_6049_);
                if v___x_6050_ == 0 {
                    v___x_6051_ = lean_unsigned_to_nat(1);
                    v_size_x27_6052_ = lean_nat_add(v_size_6031_, v___x_6051_);
                    lean_dec(v_size_6031_);
                    lean_inc(v_bkt_6049_);
                    v___x_6053_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_6053_, 0, v_a_6029_);
                    lean_ctor_set(v___x_6053_, 1, v_b_6030_);
                    lean_ctor_set(v___x_6053_, 2, v_bkt_6049_);
                    v_buckets_x27_6054_ =
                        lean_array_uset(v_buckets_6032_, v___x_6048_, v___x_6053_);
                    v___x_6055_ = lean_unsigned_to_nat(4);
                    v___x_6056_ = lean_nat_mul(v_size_x27_6052_, v___x_6055_);
                    v___x_6057_ = lean_unsigned_to_nat(3);
                    v___x_6058_ = lean_nat_div(v___x_6056_, v___x_6057_);
                    lean_dec(v___x_6056_);
                    v___x_6059_ = lean_array_get_size(v_buckets_x27_6054_);
                    v___x_6060_ = lean_nat_dec_le(v___x_6058_, v___x_6059_);
                    lean_dec(v___x_6058_);
                    if v___x_6060_ == 0 {
                        v_val_6061_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2___redArg(v_buckets_x27_6054_);
                        if v_isShared_6035_ == 0 {
                            lean_ctor_set(v___x_6034_, 1, v_val_6061_);
                            lean_ctor_set(v___x_6034_, 0, v_size_x27_6052_);
                            v___x_6063_ = v___x_6034_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6064_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_size_x27_6052_);
                            lean_ctor_set(v_reuseFailAlloc_6064_, 1, v_val_6061_);
                            v___x_6063_ = v_reuseFailAlloc_6064_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_6035_ == 0 {
                            lean_ctor_set(v___x_6034_, 1, v_buckets_x27_6054_);
                            lean_ctor_set(v___x_6034_, 0, v_size_x27_6052_);
                            v___x_6066_ = v___x_6034_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6067_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6067_, 0, v_size_x27_6052_);
                            lean_ctor_set(v_reuseFailAlloc_6067_, 1, v_buckets_x27_6054_);
                            v___x_6066_ = v_reuseFailAlloc_6067_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_6049_);
                    v___x_6068_ = lean_box(0);
                    v_buckets_x27_6069_ =
                        lean_array_uset(v_buckets_6032_, v___x_6048_, v___x_6068_);
                    v___x_6070_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__3___redArg(v_a_6029_, v_b_6030_, v_bkt_6049_);
                    v___x_6071_ = lean_array_uset(v_buckets_x27_6069_, v___x_6048_, v___x_6070_);
                    if v_isShared_6035_ == 0 {
                        lean_ctor_set(v___x_6034_, 1, v___x_6071_);
                        v___x_6073_ = v___x_6034_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6074_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_size_6031_);
                        lean_ctor_set(v_reuseFailAlloc_6074_, 1, v___x_6071_);
                        v___x_6073_ = v_reuseFailAlloc_6074_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6063_;
            }
            3 => {
                return v___x_6066_;
            }
            4 => {
                return v___x_6073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet(
    mut v_decl_6079_: *mut LeanObject,
    mut v_k_6080_: *mut LeanObject,
    mut v_a_6081_: *mut LeanObject,
    mut v_a_6082_: *mut LeanObject,
    mut v_a_6083_: *mut LeanObject,
    mut v_a_6084_: *mut LeanObject,
    mut v_a_6085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sizeId_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6120_: u8 = 0;
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: u8 = 0;
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: u8 = 0;
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: u8 = 0;
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6138_: u8 = 0;
    let mut v_str_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: u8 = 0;
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: u8 = 0;
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elems_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remainingCapacity_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6151_: u8 = 0;
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6170_: u8 = 0;
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6175_: u8 = 0;
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: u8 = 0;
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: u8 = 0;
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: u8 = 0;
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: u8 = 0;
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6201_: u8 = 0;
    let mut v_value_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6205_: u8 = 0;
    let mut v_declName_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6211_: u8 = 0;
    let mut v_us_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: u8 = 0;
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: u8 = 0;
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6232_: u8 = 0;
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6240_: u8 = 0;
    let mut v_unused_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6242_: u8 = 0;
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6245_: u8 = 0;
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut v_val_6254_: u16 = 0;
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6265_: u8 = 0;
    let mut v_val_6266_: u32 = 0;
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6269_: u8 = 0;
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6277_: u8 = 0;
    let mut v_val_6278_: u64 = 0;
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6281_: u8 = 0;
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6289_: u8 = 0;
    let mut v_val_6290_: u64 = 0;
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6293_: u8 = 0;
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6301_: u8 = 0;
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v_i_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: u8 = 0;
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6310_: u8 = 0;
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: u8 = 0;
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: u8 = 0;
    let mut v_isSharedCheck_6337_: u8 = 0;
    let mut v_a_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6341_: u8 = 0;
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6345_: u8 = 0;
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6356_: u8 = 0;
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6364_: u16 = 0;
    let mut v___x_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_6096_ = lean_ctor_get(v_decl_6079_, 0);
                lean_inc(v_fvarId_6096_);
                v_type_6097_ = lean_ctor_get(v_decl_6079_, 2);
                lean_inc_ref(v_type_6097_);
                v_value_6098_ = lean_ctor_get(v_decl_6079_, 3);
                lean_inc(v_value_6098_);
                lean_dec_ref(v_decl_6079_);
                match lean_obj_tag(v_value_6098_) {
                    9 => {
                        lean_dec_ref(v_type_6097_);
                        v_fn_6116_ = lean_ctor_get(v_value_6098_, 0);
                        v_args_6117_ = lean_ctor_get(v_value_6098_, 1);
                        v_isSharedCheck_6201_ = (!lean_is_exclusive(v_value_6098_)) as u8;
                        if v_isSharedCheck_6201_ == 0 {
                            v___x_6119_ = v_value_6098_;
                            v_isShared_6120_ = v_isSharedCheck_6201_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_args_6117_);
                            lean_inc(v_fn_6116_);
                            lean_dec(v_value_6098_);
                            v___x_6119_ = lean_box(0);
                            v_isShared_6120_ = v_isSharedCheck_6201_;
                            state = 5;
                            continue;
                        }
                    }
                    0 => {
                        v_value_6202_ = lean_ctor_get(v_value_6098_, 0);
                        v_isSharedCheck_6302_ = (!lean_is_exclusive(v_value_6098_)) as u8;
                        if v_isSharedCheck_6302_ == 0 {
                            v___x_6204_ = v_value_6098_;
                            v_isShared_6205_ = v_isSharedCheck_6302_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_value_6202_);
                            lean_dec(v_value_6098_);
                            v___x_6204_ = lean_box(0);
                            v_isShared_6205_ = v_isSharedCheck_6302_;
                            state = 12;
                            continue;
                        }
                    }
                    5 => {
                        lean_dec_ref(v_type_6097_);
                        v_i_6303_ = lean_ctor_get(v_value_6098_, 0);
                        lean_inc_ref(v_i_6303_);
                        v_args_6304_ = lean_ctor_get(v_value_6098_, 1);
                        lean_inc_ref(v_args_6304_);
                        lean_dec_ref_known(v_value_6098_, 2);
                        v___x_6305_ = l_Lean_Compiler_LCNF_CtorInfo_isScalar(v_i_6303_);
                        if v___x_6305_ == 0 {
                            v___x_6306_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileArgs(v_args_6304_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                            if lean_obj_tag(v___x_6306_) == 0 {
                                v_a_6307_ = lean_ctor_get(v___x_6306_, 0);
                                v_isSharedCheck_6337_ = (!lean_is_exclusive(v___x_6306_)) as u8;
                                if v_isSharedCheck_6337_ == 0 {
                                    v___x_6309_ = v___x_6306_;
                                    v_isShared_6310_ = v_isSharedCheck_6337_;
                                    state = 29;
                                    continue;
                                } else {
                                    lean_inc(v_a_6307_);
                                    lean_dec(v___x_6306_);
                                    v___x_6309_ = lean_box(0);
                                    v_isShared_6310_ = v_isSharedCheck_6337_;
                                    state = 29;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_i_6303_);
                                lean_dec(v_fvarId_6096_);
                                lean_dec_ref(v_k_6080_);
                                v_a_6338_ = lean_ctor_get(v___x_6306_, 0);
                                v_isSharedCheck_6345_ = (!lean_is_exclusive(v___x_6306_)) as u8;
                                if v_isSharedCheck_6345_ == 0 {
                                    v___x_6340_ = v___x_6306_;
                                    v_isShared_6341_ = v_isSharedCheck_6345_;
                                    state = 33;
                                    continue;
                                } else {
                                    lean_inc(v_a_6338_);
                                    lean_dec(v___x_6306_);
                                    v___x_6340_ = lean_box(0);
                                    v_isShared_6341_ = v_isSharedCheck_6345_;
                                    state = 33;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_args_6304_);
                            v___x_6346_ = lean_st_ref_take(v_a_6081_);
                            v_cidx_6347_ = lean_ctor_get(v_i_6303_, 1);
                            lean_inc(v_cidx_6347_);
                            lean_dec_ref(v_i_6303_);
                            v___x_6348_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_6348_, 0, v_cidx_6347_);
                            v___x_6349_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_6349_, 0, v___x_6348_);
                            v___x_6350_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6346_, v_fvarId_6096_, v___x_6349_);
                            v___x_6351_ = lean_st_ref_set(v_a_6081_, v___x_6350_);
                            v___x_6352_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                            return v___x_6352_;
                        }
                    }
                    13 => {
                        lean_dec_ref(v_type_6097_);
                        v_fvarId_6353_ = lean_ctor_get(v_value_6098_, 1);
                        lean_inc(v_fvarId_6353_);
                        lean_dec_ref_known(v_value_6098_, 2);
                        v___x_6354_ = lean_st_ref_get(v_a_6081_);
                        v___x_6355_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_6354_, v_fvarId_6353_);
                        lean_dec(v_fvarId_6353_);
                        lean_dec(v___x_6354_);
                        match lean_obj_tag(v___x_6355_) {
                            1 => {
                                v_val_6356_ = lean_ctor_get_uint8(v___x_6355_, 0 as u32);
                                lean_dec_ref_known(v___x_6355_, 0);
                                v___x_6357_ = lean_st_ref_take(v_a_6081_);
                                v___x_6358_ = lean_uint8_to_nat(v_val_6356_);
                                v___x_6359_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6359_, 0, v___x_6358_);
                                v___x_6360_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6360_, 0, v___x_6359_);
                                v___x_6361_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6357_, v_fvarId_6096_, v___x_6360_);
                                v___x_6362_ = lean_st_ref_set(v_a_6081_, v___x_6361_);
                                v___x_6363_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                                return v___x_6363_;
                            }
                            2 => {
                                v_val_6364_ = lean_ctor_get_uint16(v___x_6355_, 0 as u32);
                                lean_dec_ref_known(v___x_6355_, 0);
                                v___x_6365_ = lean_st_ref_take(v_a_6081_);
                                v___x_6366_ = lean_uint16_to_nat(v_val_6364_);
                                v___x_6367_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6367_, 0, v___x_6366_);
                                v___x_6368_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6368_, 0, v___x_6367_);
                                v___x_6369_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6365_, v_fvarId_6096_, v___x_6368_);
                                v___x_6370_ = lean_st_ref_set(v_a_6081_, v___x_6369_);
                                v___x_6371_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                                return v___x_6371_;
                            }
                            _ => {
                                lean_dec_ref(v___x_6355_);
                                lean_dec(v_fvarId_6096_);
                                lean_dec_ref(v_k_6080_);
                                v___x_6372_ = lean_box(0);
                                v___x_6373_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6373_, 0, v___x_6372_);
                                return v___x_6373_;
                            }
                        }
                    }
                    _ => {
                        lean_dec(v_value_6098_);
                        lean_dec_ref(v_type_6097_);
                        lean_dec(v_fvarId_6096_);
                        lean_dec_ref(v_k_6080_);
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6088_ = lean_box(0);
                v___x_6089_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6089_, 0, v___x_6088_);
                return v___x_6089_;
            }
            2 => {
                v___x_6091_ = lean_box(0);
                v___x_6092_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6092_, 0, v___x_6091_);
                return v___x_6092_;
            }
            3 => {
                v___x_6094_ = lean_box(0);
                v___x_6095_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6095_, 0, v___x_6094_);
                return v___x_6095_;
            }
            4 => {
                v___x_6106_ = lean_st_ref_get(v___y_6101_);
                v___x_6107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_6106_, v_sizeId_6100_);
                lean_dec(v_sizeId_6100_);
                lean_dec(v___x_6106_);
                if lean_obj_tag(v___x_6107_) == 0 {
                    v_arg_6108_ = lean_ctor_get(v___x_6107_, 0);
                    lean_inc_ref(v_arg_6108_);
                    lean_dec_ref_known(v___x_6107_, 1);
                    if lean_obj_tag(v_arg_6108_) == 0 {
                        v_val_6109_ = lean_ctor_get(v_arg_6108_, 0);
                        lean_inc(v_val_6109_);
                        lean_dec_ref_known(v_arg_6108_, 1);
                        v___x_6110_ = lean_st_ref_take(v___y_6101_);
                        v___x_6111_ = lean_box(0);
                        v___x_6112_ = lean_alloc_ctor(6, 2, (0) as u32);
                        lean_ctor_set(v___x_6112_, 0, v___x_6111_);
                        lean_ctor_set(v___x_6112_, 1, v_val_6109_);
                        v___x_6113_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6110_, v_fvarId_6096_, v___x_6112_);
                        v___x_6114_ = lean_st_ref_set(v___y_6101_, v___x_6113_);
                        v___x_6115_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_);
                        return v___x_6115_;
                    } else {
                        lean_dec_ref(v_arg_6108_);
                        lean_dec(v_fvarId_6096_);
                        lean_dec_ref(v_k_6080_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_6107_);
                    lean_dec(v_fvarId_6096_);
                    lean_dec_ref(v_k_6080_);
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_6121_ = lean_array_get_size(v_args_6117_);
                v___x_6122_ = lean_unsigned_to_nat(0);
                v___x_6123_ = lean_nat_dec_eq(v___x_6121_, v___x_6122_);
                if v___x_6123_ == 0 {
                    v___x_6124_ = lean_unsigned_to_nat(2);
                    v___x_6125_ = lean_nat_dec_eq(v___x_6121_, v___x_6124_);
                    if v___x_6125_ == 0 {
                        v___x_6126_ = lean_unsigned_to_nat(3);
                        v___x_6127_ = lean_nat_dec_eq(v___x_6121_, v___x_6126_);
                        if v___x_6127_ == 0 {
                            lean_del_object(v___x_6119_);
                            lean_dec_ref(v_args_6117_);
                            lean_dec(v_fn_6116_);
                            lean_dec(v_fvarId_6096_);
                            lean_dec_ref(v_k_6080_);
                            state = 3;
                            continue;
                        } else {
                            v___x_6128_ = lean_array_fget_borrowed(v_args_6117_, v___x_6122_);
                            if lean_obj_tag(v___x_6128_) == 0 {
                                v___x_6129_ = lean_unsigned_to_nat(1);
                                v___x_6130_ = lean_array_fget_borrowed(v_args_6117_, v___x_6129_);
                                if lean_obj_tag(v___x_6130_) == 1 {
                                    v_fvarId_6131_ = lean_ctor_get(v___x_6130_, 0);
                                    lean_inc(v_fvarId_6131_);
                                    v___x_6132_ = lean_array_fget(v_args_6117_, v___x_6124_);
                                    lean_dec_ref(v_args_6117_);
                                    if lean_obj_tag(v___x_6132_) == 1 {
                                        if lean_obj_tag(v_fn_6116_) == 1 {
                                            v_pre_6133_ = lean_ctor_get(v_fn_6116_, 0);
                                            lean_inc(v_pre_6133_);
                                            if lean_obj_tag(v_pre_6133_) == 1 {
                                                v_pre_6134_ = lean_ctor_get(v_pre_6133_, 0);
                                                if lean_obj_tag(v_pre_6134_) == 0 {
                                                    v_fvarId_6135_ = lean_ctor_get(v___x_6132_, 0);
                                                    v_isSharedCheck_6175_ =
                                                        (!lean_is_exclusive(v___x_6132_)) as u8;
                                                    if v_isSharedCheck_6175_ == 0 {
                                                        v___x_6137_ = v___x_6132_;
                                                        v_isShared_6138_ = v_isSharedCheck_6175_;
                                                        state = 6;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_fvarId_6135_);
                                                        lean_dec(v___x_6132_);
                                                        v___x_6137_ = lean_box(0);
                                                        v_isShared_6138_ = v_isSharedCheck_6175_;
                                                        state = 6;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v_pre_6133_, 2);
                                                    lean_dec_ref_known(v_fn_6116_, 2);
                                                    lean_dec_ref_known(v___x_6132_, 1);
                                                    lean_dec(v_fvarId_6131_);
                                                    lean_del_object(v___x_6119_);
                                                    lean_dec(v_fvarId_6096_);
                                                    lean_dec_ref(v_k_6080_);
                                                    state = 3;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref_known(v_fn_6116_, 2);
                                                lean_dec(v_pre_6133_);
                                                lean_dec_ref_known(v___x_6132_, 1);
                                                lean_dec(v_fvarId_6131_);
                                                lean_del_object(v___x_6119_);
                                                lean_dec(v_fvarId_6096_);
                                                lean_dec_ref(v_k_6080_);
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v___x_6132_, 1);
                                            lean_dec(v_fvarId_6131_);
                                            lean_del_object(v___x_6119_);
                                            lean_dec(v_fn_6116_);
                                            lean_dec(v_fvarId_6096_);
                                            lean_dec_ref(v_k_6080_);
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_6132_);
                                        lean_dec(v_fvarId_6131_);
                                        lean_del_object(v___x_6119_);
                                        lean_dec(v_fn_6116_);
                                        lean_dec(v_fvarId_6096_);
                                        lean_dec_ref(v_k_6080_);
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_6119_);
                                    lean_dec_ref(v_args_6117_);
                                    lean_dec(v_fn_6116_);
                                    lean_dec(v_fvarId_6096_);
                                    lean_dec_ref(v_k_6080_);
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_6119_);
                                lean_dec_ref(v_args_6117_);
                                lean_dec(v_fn_6116_);
                                lean_dec(v_fvarId_6096_);
                                lean_dec_ref(v_k_6080_);
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_6119_);
                        v___x_6176_ = lean_array_fget_borrowed(v_args_6117_, v___x_6122_);
                        if lean_obj_tag(v___x_6176_) == 0 {
                            v___x_6177_ = lean_unsigned_to_nat(1);
                            v___x_6178_ = lean_array_fget(v_args_6117_, v___x_6177_);
                            lean_dec_ref(v_args_6117_);
                            if lean_obj_tag(v___x_6178_) == 1 {
                                if lean_obj_tag(v_fn_6116_) == 1 {
                                    v_pre_6179_ = lean_ctor_get(v_fn_6116_, 0);
                                    lean_inc(v_pre_6179_);
                                    if lean_obj_tag(v_pre_6179_) == 1 {
                                        v_pre_6180_ = lean_ctor_get(v_pre_6179_, 0);
                                        if lean_obj_tag(v_pre_6180_) == 0 {
                                            v_fvarId_6181_ = lean_ctor_get(v___x_6178_, 0);
                                            lean_inc(v_fvarId_6181_);
                                            lean_dec_ref_known(v___x_6178_, 1);
                                            v_str_6182_ = lean_ctor_get(v_fn_6116_, 1);
                                            lean_inc_ref(v_str_6182_);
                                            lean_dec_ref_known(v_fn_6116_, 2);
                                            v_str_6183_ = lean_ctor_get(v_pre_6179_, 1);
                                            lean_inc_ref(v_str_6183_);
                                            lean_dec_ref_known(v_pre_6179_, 2);
                                            v___x_6184_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__17;
                                            v___x_6185_ =
                                                lean_string_dec_eq(v_str_6183_, v___x_6184_);
                                            lean_dec_ref(v_str_6183_);
                                            if v___x_6185_ == 0 {
                                                lean_dec_ref(v_str_6182_);
                                                lean_dec(v_fvarId_6181_);
                                                lean_dec(v_fvarId_6096_);
                                                lean_dec_ref(v_k_6080_);
                                                state = 3;
                                                continue;
                                            } else {
                                                v___x_6186_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__20;
                                                v___x_6187_ =
                                                    lean_string_dec_eq(v_str_6182_, v___x_6186_);
                                                if v___x_6187_ == 0 {
                                                    v___x_6188_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__21;
                                                    v___x_6189_ = lean_string_dec_eq(
                                                        v_str_6182_,
                                                        v___x_6188_,
                                                    );
                                                    lean_dec_ref(v_str_6182_);
                                                    if v___x_6189_ == 0 {
                                                        lean_dec(v_fvarId_6181_);
                                                        lean_dec(v_fvarId_6096_);
                                                        lean_dec_ref(v_k_6080_);
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        v_sizeId_6100_ = v_fvarId_6181_;
                                                        v___y_6101_ = v_a_6081_;
                                                        v___y_6102_ = v_a_6082_;
                                                        v___y_6103_ = v_a_6083_;
                                                        v___y_6104_ = v_a_6084_;
                                                        v___y_6105_ = v_a_6085_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_str_6182_);
                                                    v_sizeId_6100_ = v_fvarId_6181_;
                                                    v___y_6101_ = v_a_6081_;
                                                    v___y_6102_ = v_a_6082_;
                                                    v___y_6103_ = v_a_6083_;
                                                    v___y_6104_ = v_a_6084_;
                                                    v___y_6105_ = v_a_6085_;
                                                    state = 4;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref_known(v_pre_6179_, 2);
                                            lean_dec_ref_known(v_fn_6116_, 2);
                                            lean_dec_ref_known(v___x_6178_, 1);
                                            lean_dec(v_fvarId_6096_);
                                            lean_dec_ref(v_k_6080_);
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_fn_6116_, 2);
                                        lean_dec(v_pre_6179_);
                                        lean_dec_ref_known(v___x_6178_, 1);
                                        lean_dec(v_fvarId_6096_);
                                        lean_dec_ref(v_k_6080_);
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_6178_, 1);
                                    lean_dec(v_fn_6116_);
                                    lean_dec(v_fvarId_6096_);
                                    lean_dec_ref(v_k_6080_);
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_6178_);
                                lean_dec(v_fn_6116_);
                                lean_dec(v_fvarId_6096_);
                                lean_dec_ref(v_k_6080_);
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_args_6117_);
                            lean_dec(v_fn_6116_);
                            lean_dec(v_fvarId_6096_);
                            lean_dec_ref(v_k_6080_);
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_6119_);
                    lean_dec_ref(v_args_6117_);
                    v___x_6190_ = lean_st_ref_get(v_a_6085_);
                    v_env_6191_ = lean_ctor_get(v___x_6190_, 0);
                    lean_inc_ref(v_env_6191_);
                    lean_dec(v___x_6190_);
                    v___x_6192_ = l_Lean_Compiler_LCNF_isSimpleGroundDecl(v_env_6191_, v_fn_6116_);
                    if v___x_6192_ == 0 {
                        lean_dec(v_fn_6116_);
                        lean_dec(v_fvarId_6096_);
                        lean_dec_ref(v_k_6080_);
                        v___x_6193_ = lean_box(0);
                        v___x_6194_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6194_, 0, v___x_6193_);
                        return v___x_6194_;
                    } else {
                        v___x_6195_ = lean_st_ref_take(v_a_6081_);
                        v___x_6196_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6196_, 0, v_fn_6116_);
                        v___x_6197_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6197_, 0, v___x_6196_);
                        v___x_6198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6195_, v_fvarId_6096_, v___x_6197_);
                        v___x_6199_ = lean_st_ref_set(v_a_6081_, v___x_6198_);
                        v___x_6200_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                        return v___x_6200_;
                    }
                }
            }
            6 => {
                v_str_6139_ = lean_ctor_get(v_fn_6116_, 1);
                lean_inc_ref(v_str_6139_);
                lean_dec_ref_known(v_fn_6116_, 2);
                v_str_6140_ = lean_ctor_get(v_pre_6133_, 1);
                lean_inc_ref(v_str_6140_);
                lean_dec_ref_known(v_pre_6133_, 2);
                v___x_6141_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__17;
                v___x_6142_ = lean_string_dec_eq(v_str_6140_, v___x_6141_);
                lean_dec_ref(v_str_6140_);
                if v___x_6142_ == 0 {
                    lean_dec_ref(v_str_6139_);
                    lean_del_object(v___x_6137_);
                    lean_dec(v_fvarId_6135_);
                    lean_dec(v_fvarId_6131_);
                    lean_del_object(v___x_6119_);
                    lean_dec(v_fvarId_6096_);
                    lean_dec_ref(v_k_6080_);
                    state = 3;
                    continue;
                } else {
                    v___x_6143_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet___closed__22;
                    v___x_6144_ = lean_string_dec_eq(v_str_6139_, v___x_6143_);
                    lean_dec_ref(v_str_6139_);
                    if v___x_6144_ == 0 {
                        lean_del_object(v___x_6137_);
                        lean_dec(v_fvarId_6135_);
                        lean_dec(v_fvarId_6131_);
                        lean_del_object(v___x_6119_);
                        lean_dec(v_fvarId_6096_);
                        lean_dec_ref(v_k_6080_);
                        state = 3;
                        continue;
                    } else {
                        v___x_6145_ = lean_st_ref_get(v_a_6081_);
                        v___x_6146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_6145_, v_fvarId_6131_);
                        lean_dec(v_fvarId_6131_);
                        lean_dec(v___x_6145_);
                        if lean_obj_tag(v___x_6146_) == 6 {
                            v_elems_6147_ = lean_ctor_get(v___x_6146_, 0);
                            v_remainingCapacity_6148_ = lean_ctor_get(v___x_6146_, 1);
                            v_isSharedCheck_6170_ = (!lean_is_exclusive(v___x_6146_)) as u8;
                            if v_isSharedCheck_6170_ == 0 {
                                v___x_6150_ = v___x_6146_;
                                v_isShared_6151_ = v_isSharedCheck_6170_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_remainingCapacity_6148_);
                                lean_inc(v_elems_6147_);
                                lean_dec(v___x_6146_);
                                v___x_6150_ = lean_box(0);
                                v_isShared_6151_ = v_isSharedCheck_6170_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_6146_);
                            lean_dec(v_fvarId_6135_);
                            lean_del_object(v___x_6119_);
                            lean_dec(v_fvarId_6096_);
                            lean_dec_ref(v_k_6080_);
                            v___x_6171_ = lean_box(0);
                            if v_isShared_6138_ == 0 {
                                lean_ctor_set_tag(v___x_6137_, 0);
                                lean_ctor_set(v___x_6137_, 0, v___x_6171_);
                                v___x_6173_ = v___x_6137_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_6174_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6174_, 0, v___x_6171_);
                                v___x_6173_ = v_reuseFailAlloc_6174_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                v___x_6152_ = lean_st_ref_get(v_a_6081_);
                v___x_6153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain_spec__0(v___x_6152_, v_fvarId_6135_);
                lean_dec(v_fvarId_6135_);
                lean_dec(v___x_6152_);
                if lean_obj_tag(v___x_6153_) == 0 {
                    lean_del_object(v___x_6137_);
                    v_arg_6154_ = lean_ctor_get(v___x_6153_, 0);
                    lean_inc_ref(v_arg_6154_);
                    lean_dec_ref_known(v___x_6153_, 1);
                    v___x_6155_ = lean_st_ref_take(v_a_6081_);
                    if v_isShared_6120_ == 0 {
                        lean_ctor_set_tag(v___x_6119_, 1);
                        lean_ctor_set(v___x_6119_, 1, v_elems_6147_);
                        lean_ctor_set(v___x_6119_, 0, v_arg_6154_);
                        v___x_6157_ = v___x_6119_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6165_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6165_, 0, v_arg_6154_);
                        lean_ctor_set(v_reuseFailAlloc_6165_, 1, v_elems_6147_);
                        v___x_6157_ = v_reuseFailAlloc_6165_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_6153_);
                    lean_del_object(v___x_6150_);
                    lean_dec(v_remainingCapacity_6148_);
                    lean_dec(v_elems_6147_);
                    lean_del_object(v___x_6119_);
                    lean_dec(v_fvarId_6096_);
                    lean_dec_ref(v_k_6080_);
                    v___x_6166_ = lean_box(0);
                    if v_isShared_6138_ == 0 {
                        lean_ctor_set_tag(v___x_6137_, 0);
                        lean_ctor_set(v___x_6137_, 0, v___x_6166_);
                        v___x_6168_ = v___x_6137_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6169_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6166_);
                        v___x_6168_ = v_reuseFailAlloc_6169_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_6158_ = lean_nat_sub(v_remainingCapacity_6148_, v___x_6129_);
                lean_dec(v_remainingCapacity_6148_);
                if v_isShared_6151_ == 0 {
                    lean_ctor_set(v___x_6150_, 1, v___x_6158_);
                    lean_ctor_set(v___x_6150_, 0, v___x_6157_);
                    v___x_6160_ = v___x_6150_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6164_ = lean_alloc_ctor(6, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6164_, 0, v___x_6157_);
                    lean_ctor_set(v_reuseFailAlloc_6164_, 1, v___x_6158_);
                    v___x_6160_ = v_reuseFailAlloc_6164_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6155_, v_fvarId_6096_, v___x_6160_);
                v___x_6162_ = lean_st_ref_set(v_a_6081_, v___x_6161_);
                v___x_6163_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                return v___x_6163_;
            }
            10 => {
                return v___x_6168_;
            }
            11 => {
                return v___x_6173_;
            }
            12 => match lean_obj_tag(v_value_6202_) {
                0 => {
                    if lean_obj_tag(v_type_6097_) == 4 {
                        v_declName_6206_ = lean_ctor_get(v_type_6097_, 0);
                        lean_inc(v_declName_6206_);
                        if lean_obj_tag(v_declName_6206_) == 1 {
                            v_pre_6207_ = lean_ctor_get(v_declName_6206_, 0);
                            if lean_obj_tag(v_pre_6207_) == 0 {
                                v_val_6208_ = lean_ctor_get(v_value_6202_, 0);
                                v_isSharedCheck_6232_ = (!lean_is_exclusive(v_value_6202_)) as u8;
                                if v_isSharedCheck_6232_ == 0 {
                                    v___x_6210_ = v_value_6202_;
                                    v_isShared_6211_ = v_isSharedCheck_6232_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_val_6208_);
                                    lean_dec(v_value_6202_);
                                    v___x_6210_ = lean_box(0);
                                    v_isShared_6211_ = v_isSharedCheck_6232_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_declName_6206_, 2);
                                lean_dec_ref_known(v_type_6097_, 2);
                                lean_dec_ref_known(v_value_6202_, 1);
                                lean_del_object(v___x_6204_);
                                lean_dec(v_fvarId_6096_);
                                lean_dec_ref(v_k_6080_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_type_6097_, 2);
                            lean_dec(v_declName_6206_);
                            lean_dec_ref_known(v_value_6202_, 1);
                            lean_del_object(v___x_6204_);
                            lean_dec(v_fvarId_6096_);
                            lean_dec_ref(v_k_6080_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_value_6202_, 1);
                        lean_del_object(v___x_6204_);
                        lean_dec_ref(v_type_6097_);
                        lean_dec(v_fvarId_6096_);
                        lean_dec_ref(v_k_6080_);
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_6204_);
                    lean_dec_ref(v_type_6097_);
                    lean_dec(v_fvarId_6096_);
                    lean_dec_ref(v_k_6080_);
                    v_isSharedCheck_6240_ = (!lean_is_exclusive(v_value_6202_)) as u8;
                    if v_isSharedCheck_6240_ == 0 {
                        v_unused_6241_ = lean_ctor_get(v_value_6202_, 0);
                        lean_dec(v_unused_6241_);
                        v___x_6234_ = v_value_6202_;
                        v_isShared_6235_ = v_isSharedCheck_6240_;
                        state = 17;
                        continue;
                    } else {
                        lean_dec(v_value_6202_);
                        v___x_6234_ = lean_box(0);
                        v_isShared_6235_ = v_isSharedCheck_6240_;
                        state = 17;
                        continue;
                    }
                }
                2 => {
                    lean_del_object(v___x_6204_);
                    lean_dec_ref(v_type_6097_);
                    v_val_6242_ = lean_ctor_get_uint8(v_value_6202_, 0 as u32);
                    v_isSharedCheck_6253_ = (!lean_is_exclusive(v_value_6202_)) as u8;
                    if v_isSharedCheck_6253_ == 0 {
                        v___x_6244_ = v_value_6202_;
                        v_isShared_6245_ = v_isSharedCheck_6253_;
                        state = 19;
                        continue;
                    } else {
                        lean_dec(v_value_6202_);
                        v___x_6244_ = lean_box(0);
                        v_isShared_6245_ = v_isSharedCheck_6253_;
                        state = 19;
                        continue;
                    }
                }
                3 => {
                    lean_del_object(v___x_6204_);
                    lean_dec_ref(v_type_6097_);
                    v_val_6254_ = lean_ctor_get_uint16(v_value_6202_, 0 as u32);
                    v_isSharedCheck_6265_ = (!lean_is_exclusive(v_value_6202_)) as u8;
                    if v_isSharedCheck_6265_ == 0 {
                        v___x_6256_ = v_value_6202_;
                        v_isShared_6257_ = v_isSharedCheck_6265_;
                        state = 21;
                        continue;
                    } else {
                        lean_dec(v_value_6202_);
                        v___x_6256_ = lean_box(0);
                        v_isShared_6257_ = v_isSharedCheck_6265_;
                        state = 21;
                        continue;
                    }
                }
                4 => {
                    lean_del_object(v___x_6204_);
                    lean_dec_ref(v_type_6097_);
                    v_val_6266_ = lean_ctor_get_uint32(v_value_6202_, 0 as u32);
                    v_isSharedCheck_6277_ = (!lean_is_exclusive(v_value_6202_)) as u8;
                    if v_isSharedCheck_6277_ == 0 {
                        v___x_6268_ = v_value_6202_;
                        v_isShared_6269_ = v_isSharedCheck_6277_;
                        state = 23;
                        continue;
                    } else {
                        lean_dec(v_value_6202_);
                        v___x_6268_ = lean_box(0);
                        v_isShared_6269_ = v_isSharedCheck_6277_;
                        state = 23;
                        continue;
                    }
                }
                5 => {
                    lean_del_object(v___x_6204_);
                    lean_dec_ref(v_type_6097_);
                    v_val_6278_ = lean_ctor_get_uint64(v_value_6202_, 0 as u32);
                    v_isSharedCheck_6289_ = (!lean_is_exclusive(v_value_6202_)) as u8;
                    if v_isSharedCheck_6289_ == 0 {
                        v___x_6280_ = v_value_6202_;
                        v_isShared_6281_ = v_isSharedCheck_6289_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_value_6202_);
                        v___x_6280_ = lean_box(0);
                        v_isShared_6281_ = v_isSharedCheck_6289_;
                        state = 25;
                        continue;
                    }
                }
                _ => {
                    lean_del_object(v___x_6204_);
                    lean_dec_ref(v_type_6097_);
                    v_val_6290_ = lean_ctor_get_uint64(v_value_6202_, 0 as u32);
                    v_isSharedCheck_6301_ = (!lean_is_exclusive(v_value_6202_)) as u8;
                    if v_isSharedCheck_6301_ == 0 {
                        v___x_6292_ = v_value_6202_;
                        v_isShared_6293_ = v_isSharedCheck_6301_;
                        state = 27;
                        continue;
                    } else {
                        lean_dec(v_value_6202_);
                        v___x_6292_ = lean_box(0);
                        v_isShared_6293_ = v_isSharedCheck_6301_;
                        state = 27;
                        continue;
                    }
                }
            },
            13 => {
                v_us_6212_ = lean_ctor_get(v_type_6097_, 1);
                lean_inc(v_us_6212_);
                lean_dec_ref_known(v_type_6097_, 2);
                v_str_6213_ = lean_ctor_get(v_declName_6206_, 1);
                lean_inc_ref(v_str_6213_);
                lean_dec_ref_known(v_declName_6206_, 2);
                v___x_6214_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___closed__0;
                v___x_6215_ = lean_string_dec_eq(v_str_6213_, v___x_6214_);
                lean_dec_ref(v_str_6213_);
                if v___x_6215_ == 0 {
                    lean_dec(v_us_6212_);
                    lean_del_object(v___x_6210_);
                    lean_dec(v_val_6208_);
                    lean_del_object(v___x_6204_);
                    lean_dec(v_fvarId_6096_);
                    lean_dec_ref(v_k_6080_);
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v_us_6212_) == 0 {
                        v___x_6216_ = lean_unsigned_to_nat(2147483648);
                        v___x_6217_ = lean_nat_dec_lt(v_val_6208_, v___x_6216_);
                        if v___x_6217_ == 0 {
                            lean_dec(v_val_6208_);
                            lean_del_object(v___x_6204_);
                            lean_dec(v_fvarId_6096_);
                            lean_dec_ref(v_k_6080_);
                            v___x_6218_ = lean_box(0);
                            if v_isShared_6211_ == 0 {
                                lean_ctor_set(v___x_6210_, 0, v___x_6218_);
                                v___x_6220_ = v___x_6210_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_6221_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6221_, 0, v___x_6218_);
                                v___x_6220_ = v_reuseFailAlloc_6221_;
                                state = 14;
                                continue;
                            }
                        } else {
                            v___x_6222_ = lean_st_ref_take(v_a_6081_);
                            if v_isShared_6211_ == 0 {
                                v___x_6224_ = v___x_6210_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_6231_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6231_, 0, v_val_6208_);
                                v___x_6224_ = v_reuseFailAlloc_6231_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_us_6212_);
                        lean_del_object(v___x_6210_);
                        lean_dec(v_val_6208_);
                        lean_del_object(v___x_6204_);
                        lean_dec(v_fvarId_6096_);
                        lean_dec_ref(v_k_6080_);
                        state = 1;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_6220_;
            }
            15 => {
                if v_isShared_6205_ == 0 {
                    lean_ctor_set(v___x_6204_, 0, v___x_6224_);
                    v___x_6226_ = v___x_6204_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6230_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6230_, 0, v___x_6224_);
                    v___x_6226_ = v_reuseFailAlloc_6230_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_6227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6222_, v_fvarId_6096_, v___x_6226_);
                v___x_6228_ = lean_st_ref_set(v_a_6081_, v___x_6227_);
                v___x_6229_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                return v___x_6229_;
            }
            17 => {
                v___x_6236_ = lean_box(0);
                if v_isShared_6235_ == 0 {
                    lean_ctor_set_tag(v___x_6234_, 0);
                    lean_ctor_set(v___x_6234_, 0, v___x_6236_);
                    v___x_6238_ = v___x_6234_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6239_, 0, v___x_6236_);
                    v___x_6238_ = v_reuseFailAlloc_6239_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6238_;
            }
            19 => {
                v___x_6246_ = lean_st_ref_take(v_a_6081_);
                if v_isShared_6245_ == 0 {
                    lean_ctor_set_tag(v___x_6244_, 1);
                    v___x_6248_ = v___x_6244_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6252_ = lean_alloc_ctor(1, 0, (1) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6252_, 0 as u32, v_val_6242_);
                    v___x_6248_ = v_reuseFailAlloc_6252_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_6249_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6246_, v_fvarId_6096_, v___x_6248_);
                v___x_6250_ = lean_st_ref_set(v_a_6081_, v___x_6249_);
                v___x_6251_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                return v___x_6251_;
            }
            21 => {
                v___x_6258_ = lean_st_ref_take(v_a_6081_);
                if v_isShared_6257_ == 0 {
                    lean_ctor_set_tag(v___x_6256_, 2);
                    v___x_6260_ = v___x_6256_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6264_ = lean_alloc_ctor(2, 0, (2) as u32);
                    lean_ctor_set_uint16(v_reuseFailAlloc_6264_, 0 as u32, v_val_6254_);
                    v___x_6260_ = v_reuseFailAlloc_6264_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_6261_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6258_, v_fvarId_6096_, v___x_6260_);
                v___x_6262_ = lean_st_ref_set(v_a_6081_, v___x_6261_);
                v___x_6263_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                return v___x_6263_;
            }
            23 => {
                v___x_6270_ = lean_st_ref_take(v_a_6081_);
                if v_isShared_6269_ == 0 {
                    lean_ctor_set_tag(v___x_6268_, 3);
                    v___x_6272_ = v___x_6268_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6276_ = lean_alloc_ctor(3, 0, (4) as u32);
                    lean_ctor_set_uint32(v_reuseFailAlloc_6276_, 0 as u32, v_val_6266_);
                    v___x_6272_ = v_reuseFailAlloc_6276_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_6273_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6270_, v_fvarId_6096_, v___x_6272_);
                v___x_6274_ = lean_st_ref_set(v_a_6081_, v___x_6273_);
                v___x_6275_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                return v___x_6275_;
            }
            25 => {
                v___x_6282_ = lean_st_ref_take(v_a_6081_);
                if v_isShared_6281_ == 0 {
                    lean_ctor_set_tag(v___x_6280_, 4);
                    v___x_6284_ = v___x_6280_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6288_ = lean_alloc_ctor(4, 0, (8) as u32);
                    lean_ctor_set_uint64(v_reuseFailAlloc_6288_, 0 as u32, v_val_6278_);
                    v___x_6284_ = v_reuseFailAlloc_6288_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_6285_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6282_, v_fvarId_6096_, v___x_6284_);
                v___x_6286_ = lean_st_ref_set(v_a_6081_, v___x_6285_);
                v___x_6287_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                return v___x_6287_;
            }
            27 => {
                v___x_6294_ = lean_st_ref_take(v_a_6081_);
                if v_isShared_6293_ == 0 {
                    lean_ctor_set_tag(v___x_6292_, 5);
                    v___x_6296_ = v___x_6292_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6300_ = lean_alloc_ctor(5, 0, (8) as u32);
                    lean_ctor_set_uint64(v_reuseFailAlloc_6300_, 0 as u32, v_val_6290_);
                    v___x_6296_ = v_reuseFailAlloc_6300_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_6297_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v___x_6294_, v_fvarId_6096_, v___x_6296_);
                v___x_6298_ = lean_st_ref_set(v_a_6081_, v___x_6297_);
                v___x_6299_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_k_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
                return v___x_6299_;
            }
            29 => {
                if lean_obj_tag(v_a_6307_) == 0 {
                    lean_dec_ref(v_i_6303_);
                    lean_dec(v_fvarId_6096_);
                    lean_dec_ref(v_k_6080_);
                    v___x_6311_ = lean_box(0);
                    if v_isShared_6310_ == 0 {
                        lean_ctor_set(v___x_6309_, 0, v___x_6311_);
                        v___x_6313_ = v___x_6309_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_6314_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6314_, 0, v___x_6311_);
                        v___x_6313_ = v_reuseFailAlloc_6314_;
                        state = 30;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6309_);
                    v_val_6315_ = lean_ctor_get(v_a_6307_, 0);
                    lean_inc(v_val_6315_);
                    lean_dec_ref_known(v_a_6307_, 1);
                    v_usize_6316_ = lean_ctor_get(v_i_6303_, 3);
                    v_ssize_6317_ = lean_ctor_get(v_i_6303_, 4);
                    v___x_6318_ = lean_unsigned_to_nat(0);
                    v___x_6319_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___boxed__const__1;
                    lean_inc(v_usize_6316_);
                    v___x_6320_ = lean_mk_array(v_usize_6316_, v___x_6319_);
                    v___x_6321_ = lean_unsigned_to_nat(8);
                    v___x_6322_ = lean_unsigned_to_nat(3);
                    v___x_6323_ = lean_nat_shiftr(v_ssize_6317_, v___x_6322_);
                    v___x_6324_ = lean_nat_mul(v___x_6323_, v___x_6321_);
                    lean_dec(v___x_6323_);
                    v___x_6335_ = lean_nat_mod(v_ssize_6317_, v___x_6321_);
                    v___x_6336_ = lean_nat_dec_eq(v___x_6335_, v___x_6318_);
                    lean_dec(v___x_6335_);
                    if v___x_6336_ == 0 {
                        state = 32;
                        continue;
                    } else {
                        if v___x_6305_ == 0 {
                            v___y_6326_ = v___x_6318_;
                            state = 31;
                            continue;
                        } else {
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            30 => {
                return v___x_6313_;
            }
            31 => {
                v___x_6327_ = lean_nat_mul(v___x_6321_, v___y_6326_);
                v___x_6328_ = lean_nat_add(v___x_6324_, v___x_6327_);
                lean_dec(v___x_6327_);
                lean_dec(v___x_6324_);
                v___x_6329_ = 0;
                v___x_6330_ = lean_box((v___x_6329_) as usize);
                v___x_6331_ = lean_mk_array(v___x_6328_, v___x_6330_);
                v___x_6332_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileSetChain___redArg(v_fvarId_6096_, v_i_6303_, v_val_6315_, v___x_6320_, v___x_6331_, v_k_6080_, v_a_6081_);
                lean_dec_ref(v_i_6303_);
                lean_dec(v_fvarId_6096_);
                return v___x_6332_;
            }
            32 => {
                v___x_6334_ = lean_unsigned_to_nat(1);
                v___y_6326_ = v___x_6334_;
                state = 31;
                continue;
            }
            33 => {
                if v_isShared_6341_ == 0 {
                    v___x_6343_ = v___x_6340_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6344_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6344_, 0, v_a_6338_);
                    v___x_6343_ = v_reuseFailAlloc_6344_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(
    mut v_code_6374_: *mut LeanObject,
    mut v_a_6375_: *mut LeanObject,
    mut v_a_6376_: *mut LeanObject,
    mut v_a_6377_: *mut LeanObject,
    mut v_a_6378_: *mut LeanObject,
    mut v_a_6379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: u8 = 0;
    let mut v___x_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistent_6393_: u8 = 0;
    let mut v_k_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6399_: u8 = 0;
    let mut v_fvarId_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: u8 = 0;
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6408_: u8 = 0;
    let mut v_decl_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_6412_: u8 = 0;
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6415_: u8 = 0;
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6420_: u8 = 0;
    let mut v_unused_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_6425_: u8 = 0;
    let mut v_k_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6429_: u8 = 0;
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6434_: u8 = 0;
    let mut v_decl_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_persistent_6437_: u8 = 0;
    let mut v_k_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_6374_) {
                0 => {
                    v_k_6384_ = lean_ctor_get(v_code_6374_, 1);
                    lean_inc_ref(v_k_6384_);
                    match lean_obj_tag(v_k_6384_) {
                        5 => {
                            v_decl_6385_ = lean_ctor_get(v_code_6374_, 0);
                            lean_inc_ref(v_decl_6385_);
                            lean_dec_ref_known(v_code_6374_, 2);
                            v_fvarId_6386_ = lean_ctor_get(v_k_6384_, 0);
                            lean_inc(v_fvarId_6386_);
                            lean_dec_ref_known(v_k_6384_, 1);
                            v_fvarId_6387_ = lean_ctor_get(v_decl_6385_, 0);
                            lean_inc(v_fvarId_6387_);
                            v_value_6388_ = lean_ctor_get(v_decl_6385_, 3);
                            lean_inc(v_value_6388_);
                            lean_dec_ref(v_decl_6385_);
                            v___x_6389_ = l_Lean_instBEqFVarId_beq(v_fvarId_6387_, v_fvarId_6386_);
                            lean_dec(v_fvarId_6386_);
                            lean_dec(v_fvarId_6387_);
                            if v___x_6389_ == 0 {
                                lean_dec(v_value_6388_);
                                v___x_6390_ = lean_box(0);
                                v___x_6391_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_6391_, 0, v___x_6390_);
                                return v___x_6391_;
                            } else {
                                v___x_6392_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet(v_value_6388_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_);
                                return v___x_6392_;
                            }
                        }
                        11 => {
                            v_persistent_6393_ = lean_ctor_get_uint8(
                                v_k_6384_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            );
                            if v_persistent_6393_ == 1 {
                                v_k_6394_ = lean_ctor_get(v_k_6384_, 2);
                                lean_inc_ref(v_k_6394_);
                                if lean_obj_tag(v_k_6394_) == 5 {
                                    lean_dec_ref_known(v_k_6384_, 3);
                                    v_decl_6395_ = lean_ctor_get(v_code_6374_, 0);
                                    lean_inc_ref(v_decl_6395_);
                                    lean_dec_ref_known(v_code_6374_, 2);
                                    v_fvarId_6396_ = lean_ctor_get(v_k_6394_, 0);
                                    v_isSharedCheck_6408_ = (!lean_is_exclusive(v_k_6394_)) as u8;
                                    if v_isSharedCheck_6408_ == 0 {
                                        v___x_6398_ = v_k_6394_;
                                        v_isShared_6399_ = v_isSharedCheck_6408_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_fvarId_6396_);
                                        lean_dec(v_k_6394_);
                                        v___x_6398_ = lean_box(0);
                                        v_isShared_6399_ = v_isSharedCheck_6408_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_decl_6409_ = lean_ctor_get(v_code_6374_, 0);
                                    lean_inc_ref(v_decl_6409_);
                                    lean_dec_ref_known(v_code_6374_, 2);
                                    v_fvarId_6410_ = lean_ctor_get(v_k_6384_, 0);
                                    v_n_6411_ = lean_ctor_get(v_k_6384_, 1);
                                    v_check_6412_ = lean_ctor_get_uint8(
                                        v_k_6384_,
                                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                    );
                                    v_isSharedCheck_6420_ = (!lean_is_exclusive(v_k_6384_)) as u8;
                                    if v_isSharedCheck_6420_ == 0 {
                                        v_unused_6421_ = lean_ctor_get(v_k_6384_, 2);
                                        lean_dec(v_unused_6421_);
                                        v___x_6414_ = v_k_6384_;
                                        v_isShared_6415_ = v_isSharedCheck_6420_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_n_6411_);
                                        lean_inc(v_fvarId_6410_);
                                        lean_dec(v_k_6384_);
                                        v___x_6414_ = lean_box(0);
                                        v_isShared_6415_ = v_isSharedCheck_6420_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                v_decl_6422_ = lean_ctor_get(v_code_6374_, 0);
                                lean_inc_ref(v_decl_6422_);
                                lean_dec_ref_known(v_code_6374_, 2);
                                v_fvarId_6423_ = lean_ctor_get(v_k_6384_, 0);
                                v_n_6424_ = lean_ctor_get(v_k_6384_, 1);
                                v_check_6425_ = lean_ctor_get_uint8(
                                    v_k_6384_,
                                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                );
                                v_k_6426_ = lean_ctor_get(v_k_6384_, 2);
                                v_isSharedCheck_6434_ = (!lean_is_exclusive(v_k_6384_)) as u8;
                                if v_isSharedCheck_6434_ == 0 {
                                    v___x_6428_ = v_k_6384_;
                                    v_isShared_6429_ = v_isSharedCheck_6434_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_k_6426_);
                                    lean_inc(v_n_6424_);
                                    lean_inc(v_fvarId_6423_);
                                    lean_dec(v_k_6384_);
                                    v___x_6428_ = lean_box(0);
                                    v_isShared_6429_ = v_isSharedCheck_6434_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_decl_6435_ = lean_ctor_get(v_code_6374_, 0);
                            lean_inc_ref(v_decl_6435_);
                            lean_dec_ref_known(v_code_6374_, 2);
                            v___x_6436_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet(v_decl_6435_, v_k_6384_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_);
                            return v___x_6436_;
                        }
                    }
                }
                11 => {
                    v_persistent_6437_ = lean_ctor_get_uint8(
                        v_code_6374_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    if v_persistent_6437_ == 1 {
                        v_k_6438_ = lean_ctor_get(v_code_6374_, 2);
                        lean_inc_ref(v_k_6438_);
                        lean_dec_ref_known(v_code_6374_, 3);
                        v_code_6374_ = v_k_6438_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref_known(v_code_6374_, 3);
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_code_6374_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_6382_ = lean_box(0);
                v___x_6383_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6383_, 0, v___x_6382_);
                return v___x_6383_;
            }
            2 => {
                v_fvarId_6400_ = lean_ctor_get(v_decl_6395_, 0);
                lean_inc(v_fvarId_6400_);
                v_value_6401_ = lean_ctor_get(v_decl_6395_, 3);
                lean_inc(v_value_6401_);
                lean_dec_ref(v_decl_6395_);
                v___x_6402_ = l_Lean_instBEqFVarId_beq(v_fvarId_6400_, v_fvarId_6396_);
                lean_dec(v_fvarId_6396_);
                lean_dec(v_fvarId_6400_);
                if v___x_6402_ == 0 {
                    lean_dec(v_value_6401_);
                    v___x_6403_ = lean_box(0);
                    if v_isShared_6399_ == 0 {
                        lean_ctor_set_tag(v___x_6398_, 0);
                        lean_ctor_set(v___x_6398_, 0, v___x_6403_);
                        v___x_6405_ = v___x_6398_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6406_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6406_, 0, v___x_6403_);
                        v___x_6405_ = v_reuseFailAlloc_6406_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6398_);
                    v___x_6407_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileFinalLet(v_value_6401_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_);
                    return v___x_6407_;
                }
            }
            3 => {
                return v___x_6405_;
            }
            4 => {
                if v_isShared_6415_ == 0 {
                    v___x_6417_ = v___x_6414_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6419_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_fvarId_6410_);
                    lean_ctor_set(v_reuseFailAlloc_6419_, 1, v_n_6411_);
                    lean_ctor_set(v_reuseFailAlloc_6419_, 2, v_k_6394_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6419_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_6412_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6419_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_6393_,
                    );
                    v___x_6417_ = v_reuseFailAlloc_6419_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6418_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet(v_decl_6409_, v___x_6417_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_);
                return v___x_6418_;
            }
            6 => {
                if v_isShared_6429_ == 0 {
                    v___x_6431_ = v___x_6428_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6433_ = lean_alloc_ctor(11, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6433_, 0, v_fvarId_6423_);
                    lean_ctor_set(v_reuseFailAlloc_6433_, 1, v_n_6424_);
                    lean_ctor_set(v_reuseFailAlloc_6433_, 2, v_k_6426_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6433_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_6425_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6433_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_6393_,
                    );
                    v___x_6431_ = v_reuseFailAlloc_6433_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6432_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet(v_decl_6422_, v___x_6431_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_, v_a_6379_);
                return v___x_6432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go___boxed(
    mut v_code_6440_: *mut LeanObject,
    mut v_a_6441_: *mut LeanObject,
    mut v_a_6442_: *mut LeanObject,
    mut v_a_6443_: *mut LeanObject,
    mut v_a_6444_: *mut LeanObject,
    mut v_a_6445_: *mut LeanObject,
    mut v_a_6446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6447_: *mut LeanObject = core::ptr::null_mut();
    v_res_6447_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_code_6440_, v_a_6441_, v_a_6442_, v_a_6443_, v_a_6444_, v_a_6445_);
    lean_dec(v_a_6445_);
    lean_dec_ref(v_a_6444_);
    lean_dec(v_a_6443_);
    lean_dec_ref(v_a_6442_);
    lean_dec(v_a_6441_);
    return v_res_6447_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet___boxed(
    mut v_decl_6448_: *mut LeanObject,
    mut v_k_6449_: *mut LeanObject,
    mut v_a_6450_: *mut LeanObject,
    mut v_a_6451_: *mut LeanObject,
    mut v_a_6452_: *mut LeanObject,
    mut v_a_6453_: *mut LeanObject,
    mut v_a_6454_: *mut LeanObject,
    mut v_a_6455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6456_: *mut LeanObject = core::ptr::null_mut();
    v_res_6456_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet(v_decl_6448_, v_k_6449_, v_a_6450_, v_a_6451_, v_a_6452_, v_a_6453_, v_a_6454_);
    lean_dec(v_a_6454_);
    lean_dec_ref(v_a_6453_);
    lean_dec(v_a_6452_);
    lean_dec_ref(v_a_6451_);
    lean_dec(v_a_6450_);
    return v_res_6456_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1(
    mut v_00_u03b2_6457_: *mut LeanObject,
    mut v_m_6458_: *mut LeanObject,
    mut v_a_6459_: *mut LeanObject,
    mut v_b_6460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    v___x_6461_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1___redArg(v_m_6458_, v_a_6459_, v_b_6460_);
    return v___x_6461_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1(
    mut v_00_u03b2_6462_: *mut LeanObject,
    mut v_a_6463_: *mut LeanObject,
    mut v_x_6464_: *mut LeanObject,
) -> u8 {
    let mut v___x_6465_: u8 = 0;
    v___x_6465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1___redArg(v_a_6463_, v_x_6464_);
    return v___x_6465_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1___boxed(
    mut v_00_u03b2_6466_: *mut LeanObject,
    mut v_a_6467_: *mut LeanObject,
    mut v_x_6468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6469_: u8 = 0;
    let mut v_r_6470_: *mut LeanObject = core::ptr::null_mut();
    v_res_6469_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__1(v_00_u03b2_6466_, v_a_6467_, v_x_6468_);
    lean_dec(v_x_6468_);
    lean_dec(v_a_6467_);
    v_r_6470_ = lean_box((v_res_6469_) as usize);
    return v_r_6470_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2(
    mut v_00_u03b2_6471_: *mut LeanObject,
    mut v_data_6472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    v___x_6473_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2___redArg(v_data_6472_);
    return v___x_6473_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__3(
    mut v_00_u03b2_6474_: *mut LeanObject,
    mut v_a_6475_: *mut LeanObject,
    mut v_b_6476_: *mut LeanObject,
    mut v_x_6477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    v___x_6478_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__3___redArg(v_a_6475_, v_b_6476_, v_x_6477_);
    return v___x_6478_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3(
    mut v_00_u03b2_6479_: *mut LeanObject,
    mut v_i_6480_: *mut LeanObject,
    mut v_source_6481_: *mut LeanObject,
    mut v_target_6482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    v___x_6483_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3___redArg(v_i_6480_, v_source_6481_, v_target_6482_);
    return v___x_6483_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_6484_: *mut LeanObject,
    mut v_x_6485_: *mut LeanObject,
    mut v_x_6486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    v___x_6487_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_compileNonFinalLet_spec__1_spec__2_spec__3_spec__4___redArg(v_x_6485_, v_x_6486_);
    return v___x_6487_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__0()
-> *mut LeanObject {
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    v___x_6488_ = lean_box(0);
    v___x_6489_ = lean_unsigned_to_nat(16);
    v___x_6490_ = lean_mk_array(v___x_6489_, v___x_6488_);
    return v___x_6490_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__1()
-> *mut LeanObject {
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    v___x_6491_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__0);
    v___x_6492_ = lean_unsigned_to_nat(0);
    v___x_6493_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6493_, 0, v___x_6492_);
    lean_ctor_set(v___x_6493_, 1, v___x_6491_);
    return v___x_6493_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr(
    mut v_code_6494_: *mut LeanObject,
    mut v_a_6495_: *mut LeanObject,
    mut v_a_6496_: *mut LeanObject,
    mut v_a_6497_: *mut LeanObject,
    mut v_a_6498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6506_: u8 = 0;
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6511_: u8 = 0;
    let mut v_unused_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6500_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__1_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___closed__1);
                v___x_6501_ = lean_st_mk_ref(v___x_6500_);
                v___x_6502_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr_go(v_code_6494_, v___x_6501_, v_a_6495_, v_a_6496_, v_a_6497_, v_a_6498_);
                if lean_obj_tag(v___x_6502_) == 0 {
                    v_a_6503_ = lean_ctor_get(v___x_6502_, 0);
                    lean_inc(v_a_6503_);
                    if lean_obj_tag(v_a_6503_) == 0 {
                        lean_dec(v___x_6501_);
                        return v___x_6502_;
                    } else {
                        v_isSharedCheck_6511_ = (!lean_is_exclusive(v___x_6502_)) as u8;
                        if v_isSharedCheck_6511_ == 0 {
                            v_unused_6512_ = lean_ctor_get(v___x_6502_, 0);
                            lean_dec(v_unused_6512_);
                            v___x_6505_ = v___x_6502_;
                            v_isShared_6506_ = v_isSharedCheck_6511_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_6502_);
                            v___x_6505_ = lean_box(0);
                            v_isShared_6506_ = v_isSharedCheck_6511_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_6501_);
                    return v___x_6502_;
                }
            }
            1 => {
                v___x_6507_ = lean_st_ref_get(v___x_6501_);
                lean_dec(v___x_6501_);
                lean_dec(v___x_6507_);
                if v_isShared_6506_ == 0 {
                    v___x_6509_ = v___x_6505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6510_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_a_6503_);
                    v___x_6509_ = v_reuseFailAlloc_6510_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr___boxed(
    mut v_code_6513_: *mut LeanObject,
    mut v_a_6514_: *mut LeanObject,
    mut v_a_6515_: *mut LeanObject,
    mut v_a_6516_: *mut LeanObject,
    mut v_a_6517_: *mut LeanObject,
    mut v_a_6518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6519_: *mut LeanObject = core::ptr::null_mut();
    v_res_6519_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr(v_code_6513_, v_a_6514_, v_a_6515_, v_a_6516_, v_a_6517_);
    lean_dec(v_a_6517_);
    lean_dec_ref(v_a_6516_);
    lean_dec(v_a_6515_);
    lean_dec_ref(v_a_6514_);
    return v_res_6519_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    v___x_6520_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6520_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    v___x_6521_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__0);
    v___x_6522_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6522_, 0, v___x_6521_);
    return v___x_6522_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    v___x_6523_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__1_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__1);
    v___x_6524_ = lean_unsigned_to_nat(0);
    v___x_6525_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_6525_, 0, v___x_6524_);
    lean_ctor_set(v___x_6525_, 1, v___x_6524_);
    lean_ctor_set(v___x_6525_, 2, v___x_6524_);
    lean_ctor_set(v___x_6525_, 3, v___x_6524_);
    lean_ctor_set(v___x_6525_, 4, v___x_6523_);
    lean_ctor_set(v___x_6525_, 5, v___x_6523_);
    lean_ctor_set(v___x_6525_, 6, v___x_6523_);
    lean_ctor_set(v___x_6525_, 7, v___x_6523_);
    lean_ctor_set(v___x_6525_, 8, v___x_6523_);
    lean_ctor_set(v___x_6525_, 9, v___x_6523_);
    return v___x_6525_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__3()
-> f64 {
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: f64 = 0.0;
    v___x_6526_ = lean_unsigned_to_nat(0);
    v___x_6527_ = lean_float_of_nat(v___x_6526_);
    return v___x_6527_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0(
    mut v_cls_6531_: *mut LeanObject,
    mut v_msg_6532_: *mut LeanObject,
    mut v___y_6533_: *mut LeanObject,
    mut v___y_6534_: *mut LeanObject,
    mut v___y_6535_: *mut LeanObject,
    mut v___y_6536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6546_: u8 = 0;
    let mut v_env_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6551_: u8 = 0;
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6565_: u8 = 0;
    let mut v_tid_6566_: u64 = 0;
    let mut v_traces_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6570_: u8 = 0;
    let mut v___x_6571_: u8 = 0;
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: f64 = 0.0;
    let mut v___x_6578_: u8 = 0;
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6597_: u8 = 0;
    let mut v_isSharedCheck_6598_: u8 = 0;
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_unused_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6601_: u8 = 0;
    let mut v_a_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6605_: u8 = 0;
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_6538_ = lean_ctor_get(v___y_6535_, 2);
                v_ref_6539_ = lean_ctor_get(v___y_6535_, 5);
                v___x_6540_ = lean_st_ref_get(v___y_6536_);
                v___x_6541_ = lean_st_ref_get(v___y_6534_);
                v___x_6542_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_6533_);
                if lean_obj_tag(v___x_6542_) == 0 {
                    v_a_6543_ = lean_ctor_get(v___x_6542_, 0);
                    v_isSharedCheck_6601_ = (!lean_is_exclusive(v___x_6542_)) as u8;
                    if v_isSharedCheck_6601_ == 0 {
                        v___x_6545_ = v___x_6542_;
                        v_isShared_6546_ = v_isSharedCheck_6601_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6543_);
                        lean_dec(v___x_6542_);
                        v___x_6545_ = lean_box(0);
                        v_isShared_6546_ = v_isSharedCheck_6601_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6541_);
                    lean_dec(v___x_6540_);
                    lean_dec_ref(v_msg_6532_);
                    lean_dec(v_cls_6531_);
                    v_a_6602_ = lean_ctor_get(v___x_6542_, 0);
                    v_isSharedCheck_6609_ = (!lean_is_exclusive(v___x_6542_)) as u8;
                    if v_isSharedCheck_6609_ == 0 {
                        v___x_6604_ = v___x_6542_;
                        v_isShared_6605_ = v_isSharedCheck_6609_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6602_);
                        lean_dec(v___x_6542_);
                        v___x_6604_ = lean_box(0);
                        v_isShared_6605_ = v_isSharedCheck_6609_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_6547_ = lean_ctor_get(v___x_6540_, 0);
                lean_inc_ref(v_env_6547_);
                lean_dec(v___x_6540_);
                v_lctx_6548_ = lean_ctor_get(v___x_6541_, 0);
                v_isSharedCheck_6599_ = (!lean_is_exclusive(v___x_6541_)) as u8;
                if v_isSharedCheck_6599_ == 0 {
                    v_unused_6600_ = lean_ctor_get(v___x_6541_, 1);
                    lean_dec(v_unused_6600_);
                    v___x_6550_ = v___x_6541_;
                    v_isShared_6551_ = v_isSharedCheck_6599_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_6548_);
                    lean_dec(v___x_6541_);
                    v___x_6550_ = lean_box(0);
                    v_isShared_6551_ = v_isSharedCheck_6599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6552_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__2_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__2);
                v___x_6553_ = lean_st_ref_take(v___y_6536_);
                v_traceState_6554_ = lean_ctor_get(v___x_6553_, 4);
                v_env_6555_ = lean_ctor_get(v___x_6553_, 0);
                v_nextMacroScope_6556_ = lean_ctor_get(v___x_6553_, 1);
                v_ngen_6557_ = lean_ctor_get(v___x_6553_, 2);
                v_auxDeclNGen_6558_ = lean_ctor_get(v___x_6553_, 3);
                v_cache_6559_ = lean_ctor_get(v___x_6553_, 5);
                v_messages_6560_ = lean_ctor_get(v___x_6553_, 6);
                v_infoState_6561_ = lean_ctor_get(v___x_6553_, 7);
                v_snapshotTasks_6562_ = lean_ctor_get(v___x_6553_, 8);
                v_isSharedCheck_6598_ = (!lean_is_exclusive(v___x_6553_)) as u8;
                if v_isSharedCheck_6598_ == 0 {
                    v___x_6564_ = v___x_6553_;
                    v_isShared_6565_ = v_isSharedCheck_6598_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6562_);
                    lean_inc(v_infoState_6561_);
                    lean_inc(v_messages_6560_);
                    lean_inc(v_cache_6559_);
                    lean_inc(v_traceState_6554_);
                    lean_inc(v_auxDeclNGen_6558_);
                    lean_inc(v_ngen_6557_);
                    lean_inc(v_nextMacroScope_6556_);
                    lean_inc(v_env_6555_);
                    lean_dec(v___x_6553_);
                    v___x_6564_ = lean_box(0);
                    v_isShared_6565_ = v_isSharedCheck_6598_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_6566_ = lean_ctor_get_uint64(
                    v_traceState_6554_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_6567_ = lean_ctor_get(v_traceState_6554_, 0);
                v_isSharedCheck_6597_ = (!lean_is_exclusive(v_traceState_6554_)) as u8;
                if v_isSharedCheck_6597_ == 0 {
                    v___x_6569_ = v_traceState_6554_;
                    v_isShared_6570_ = v_isSharedCheck_6597_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_traces_6567_);
                    lean_dec(v_traceState_6554_);
                    v___x_6569_ = lean_box(0);
                    v_isShared_6570_ = v_isSharedCheck_6597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6571_ = (lean_unbox(v_a_6543_) as u8);
                lean_dec(v_a_6543_);
                v___x_6572_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_6548_, v___x_6571_);
                lean_dec_ref(v_lctx_6548_);
                lean_inc_ref(v_options_6538_);
                v___x_6573_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_6573_, 0, v_env_6547_);
                lean_ctor_set(v___x_6573_, 1, v___x_6552_);
                lean_ctor_set(v___x_6573_, 2, v___x_6572_);
                lean_ctor_set(v___x_6573_, 3, v_options_6538_);
                if v_isShared_6551_ == 0 {
                    lean_ctor_set_tag(v___x_6550_, 3);
                    lean_ctor_set(v___x_6550_, 1, v_msg_6532_);
                    lean_ctor_set(v___x_6550_, 0, v___x_6573_);
                    v___x_6575_ = v___x_6550_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6596_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6596_, 0, v___x_6573_);
                    lean_ctor_set(v_reuseFailAlloc_6596_, 1, v_msg_6532_);
                    v___x_6575_ = v_reuseFailAlloc_6596_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6576_ = lean_box(0);
                v___x_6577_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__3_once), _init_l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__3);
                v___x_6578_ = 0;
                v___x_6579_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__4;
                v___x_6580_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_6580_, 0, v_cls_6531_);
                lean_ctor_set(v___x_6580_, 1, v___x_6576_);
                lean_ctor_set(v___x_6580_, 2, v___x_6579_);
                lean_ctor_set_float(
                    v___x_6580_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6577_,
                );
                lean_ctor_set_float(
                    v___x_6580_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_6577_,
                );
                lean_ctor_set_uint8(
                    v___x_6580_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_6578_,
                );
                v___x_6581_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___closed__5;
                v___x_6582_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_6582_, 0, v___x_6580_);
                lean_ctor_set(v___x_6582_, 1, v___x_6575_);
                lean_ctor_set(v___x_6582_, 2, v___x_6581_);
                lean_inc(v_ref_6539_);
                v___x_6583_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6583_, 0, v_ref_6539_);
                lean_ctor_set(v___x_6583_, 1, v___x_6582_);
                v___x_6584_ = l_Lean_PersistentArray_push___redArg(v_traces_6567_, v___x_6583_);
                if v_isShared_6570_ == 0 {
                    lean_ctor_set(v___x_6569_, 0, v___x_6584_);
                    v___x_6586_ = v___x_6569_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6595_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 0, v___x_6584_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_6595_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_6566_,
                    );
                    v___x_6586_ = v_reuseFailAlloc_6595_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6565_ == 0 {
                    lean_ctor_set(v___x_6564_, 4, v___x_6586_);
                    v___x_6588_ = v___x_6564_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 0, v_env_6555_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 1, v_nextMacroScope_6556_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 2, v_ngen_6557_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 3, v_auxDeclNGen_6558_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 4, v___x_6586_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 5, v_cache_6559_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 6, v_messages_6560_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 7, v_infoState_6561_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 8, v_snapshotTasks_6562_);
                    v___x_6588_ = v_reuseFailAlloc_6594_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6589_ = lean_st_ref_set(v___y_6536_, v___x_6588_);
                v___x_6590_ = lean_box(0);
                if v_isShared_6546_ == 0 {
                    lean_ctor_set(v___x_6545_, 0, v___x_6590_);
                    v___x_6592_ = v___x_6545_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6593_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 0, v___x_6590_);
                    v___x_6592_ = v_reuseFailAlloc_6593_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6592_;
            }
            9 => {
                if v_isShared_6605_ == 0 {
                    v___x_6607_ = v___x_6604_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6608_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6608_, 0, v_a_6602_);
                    v___x_6607_ = v_reuseFailAlloc_6608_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6607_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0___boxed(
    mut v_cls_6610_: *mut LeanObject,
    mut v_msg_6611_: *mut LeanObject,
    mut v___y_6612_: *mut LeanObject,
    mut v___y_6613_: *mut LeanObject,
    mut v___y_6614_: *mut LeanObject,
    mut v___y_6615_: *mut LeanObject,
    mut v___y_6616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6617_: *mut LeanObject = core::ptr::null_mut();
    v_res_6617_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0(v_cls_6610_, v_msg_6611_, v___y_6612_, v___y_6613_, v___y_6614_, v___y_6615_);
    lean_dec(v___y_6615_);
    lean_dec_ref(v___y_6614_);
    lean_dec(v___y_6613_);
    lean_dec_ref(v___y_6612_);
    return v_res_6617_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__0()
-> *mut LeanObject {
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    v___x_6618_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6618_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__1()
-> *mut LeanObject {
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    v___x_6619_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__0_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__0);
    v___x_6620_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6620_, 0, v___x_6619_);
    return v___x_6620_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__2()
-> *mut LeanObject {
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
    v___x_6621_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__1_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__1);
    v___x_6622_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6622_, 0, v___x_6621_);
    lean_ctor_set(v___x_6622_, 1, v___x_6621_);
    return v___x_6622_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__8()
-> *mut LeanObject {
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    v___x_6631_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5;
    v___x_6632_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__7;
    v___x_6633_ = l_Lean_Name_append(v___x_6632_, v___x_6631_);
    return v___x_6633_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__10()
-> *mut LeanObject {
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    v___x_6635_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__9;
    v___x_6636_ = l_Lean_stringToMessageData(v___x_6635_);
    return v___x_6636_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__12()
-> *mut LeanObject {
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    v___x_6638_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__11;
    v___x_6639_ = l_Lean_stringToMessageData(v___x_6638_);
    return v___x_6639_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround(
    mut v_d_6640_: *mut LeanObject,
    mut v_a_6641_: *mut LeanObject,
    mut v_a_6642_: *mut LeanObject,
    mut v_a_6643_: *mut LeanObject,
    mut v_a_6644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v_name_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6669_: u8 = 0;
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6680_: u8 = 0;
    let mut v_unused_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6683_: u8 = 0;
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6690_: u8 = 0;
    let mut v_options_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6692_: u8 = 0;
    let mut v_val_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: u8 = 0;
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6709_: u8 = 0;
    let mut v_a_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6713_: u8 = 0;
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6717_: u8 = 0;
    let mut v___x_6718_: u8 = 0;
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: u8 = 0;
    let mut v_isSharedCheck_6722_: u8 = 0;
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_6646_ = lean_ctor_get(v_d_6640_, 1);
                lean_inc_ref(v_value_6646_);
                if lean_obj_tag(v_value_6646_) == 0 {
                    v_toSignature_6647_ = lean_ctor_get(v_d_6640_, 0);
                    lean_inc_ref(v_toSignature_6647_);
                    lean_dec_ref(v_d_6640_);
                    v_code_6648_ = lean_ctor_get(v_value_6646_, 0);
                    v_isSharedCheck_6722_ = (!lean_is_exclusive(v_value_6646_)) as u8;
                    if v_isSharedCheck_6722_ == 0 {
                        v___x_6650_ = v_value_6646_;
                        v_isShared_6651_ = v_isSharedCheck_6722_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_6648_);
                        lean_dec(v_value_6646_);
                        v___x_6650_ = lean_box(0);
                        v_isShared_6651_ = v_isSharedCheck_6722_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_6646_);
                    lean_dec_ref(v_d_6640_);
                    v___x_6723_ = lean_box(0);
                    v___x_6724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6724_, 0, v___x_6723_);
                    return v___x_6724_;
                }
            }
            1 => {
                v_name_6652_ = lean_ctor_get(v_toSignature_6647_, 0);
                lean_inc(v_name_6652_);
                v_type_6653_ = lean_ctor_get(v_toSignature_6647_, 2);
                lean_inc_ref(v_type_6653_);
                v_params_6654_ = lean_ctor_get(v_toSignature_6647_, 3);
                lean_inc_ref(v_params_6654_);
                lean_dec_ref(v_toSignature_6647_);
                v___x_6718_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isPossibleRef(v_type_6653_);
                lean_dec_ref(v_type_6653_);
                if v___x_6718_ == 0 {
                    lean_dec_ref(v_params_6654_);
                    v___y_6683_ = v___x_6718_;
                    state = 6;
                    continue;
                } else {
                    v___x_6719_ = lean_array_get_size(v_params_6654_);
                    lean_dec_ref(v_params_6654_);
                    v___x_6720_ = lean_unsigned_to_nat(0);
                    v___x_6721_ = lean_nat_dec_eq(v___x_6719_, v___x_6720_);
                    v___y_6683_ = v___x_6721_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v___x_6658_ = lean_st_ref_take(v___y_6657_);
                v_env_6659_ = lean_ctor_get(v___x_6658_, 0);
                v_nextMacroScope_6660_ = lean_ctor_get(v___x_6658_, 1);
                v_ngen_6661_ = lean_ctor_get(v___x_6658_, 2);
                v_auxDeclNGen_6662_ = lean_ctor_get(v___x_6658_, 3);
                v_traceState_6663_ = lean_ctor_get(v___x_6658_, 4);
                v_messages_6664_ = lean_ctor_get(v___x_6658_, 6);
                v_infoState_6665_ = lean_ctor_get(v___x_6658_, 7);
                v_snapshotTasks_6666_ = lean_ctor_get(v___x_6658_, 8);
                v_isSharedCheck_6680_ = (!lean_is_exclusive(v___x_6658_)) as u8;
                if v_isSharedCheck_6680_ == 0 {
                    v_unused_6681_ = lean_ctor_get(v___x_6658_, 5);
                    lean_dec(v_unused_6681_);
                    v___x_6668_ = v___x_6658_;
                    v_isShared_6669_ = v_isSharedCheck_6680_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6666_);
                    lean_inc(v_infoState_6665_);
                    lean_inc(v_messages_6664_);
                    lean_inc(v_traceState_6663_);
                    lean_inc(v_auxDeclNGen_6662_);
                    lean_inc(v_ngen_6661_);
                    lean_inc(v_nextMacroScope_6660_);
                    lean_inc(v_env_6659_);
                    lean_dec(v___x_6658_);
                    v___x_6668_ = lean_box(0);
                    v_isShared_6669_ = v_isSharedCheck_6680_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6670_ = l_Lean_Compiler_LCNF_addSimpleGroundDecl(
                    v_env_6659_,
                    v_name_6652_,
                    v___y_6656_,
                );
                v___x_6671_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__2_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__2);
                if v_isShared_6669_ == 0 {
                    lean_ctor_set(v___x_6668_, 5, v___x_6671_);
                    lean_ctor_set(v___x_6668_, 0, v___x_6670_);
                    v___x_6673_ = v___x_6668_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6679_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 0, v___x_6670_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 1, v_nextMacroScope_6660_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 2, v_ngen_6661_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 3, v_auxDeclNGen_6662_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 4, v_traceState_6663_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 5, v___x_6671_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 6, v_messages_6664_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 7, v_infoState_6665_);
                    lean_ctor_set(v_reuseFailAlloc_6679_, 8, v_snapshotTasks_6666_);
                    v___x_6673_ = v_reuseFailAlloc_6679_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6674_ = lean_st_ref_set(v___y_6657_, v___x_6673_);
                v___x_6675_ = lean_box(0);
                if v_isShared_6651_ == 0 {
                    lean_ctor_set(v___x_6650_, 0, v___x_6675_);
                    v___x_6677_ = v___x_6650_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6678_, 0, v___x_6675_);
                    v___x_6677_ = v_reuseFailAlloc_6678_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6677_;
            }
            6 => {
                if v___y_6683_ == 0 {
                    lean_dec(v_name_6652_);
                    lean_del_object(v___x_6650_);
                    lean_dec_ref(v_code_6648_);
                    v___x_6684_ = lean_box(0);
                    v___x_6685_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6685_, 0, v___x_6684_);
                    return v___x_6685_;
                } else {
                    v___x_6686_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_compileToSimpleGroundExpr(v_code_6648_, v_a_6641_, v_a_6642_, v_a_6643_, v_a_6644_);
                    if lean_obj_tag(v___x_6686_) == 0 {
                        v_a_6687_ = lean_ctor_get(v___x_6686_, 0);
                        v_isSharedCheck_6709_ = (!lean_is_exclusive(v___x_6686_)) as u8;
                        if v_isSharedCheck_6709_ == 0 {
                            v___x_6689_ = v___x_6686_;
                            v_isShared_6690_ = v_isSharedCheck_6709_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6687_);
                            lean_dec(v___x_6686_);
                            v___x_6689_ = lean_box(0);
                            v_isShared_6690_ = v_isSharedCheck_6709_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_name_6652_);
                        lean_del_object(v___x_6650_);
                        v_a_6710_ = lean_ctor_get(v___x_6686_, 0);
                        v_isSharedCheck_6717_ = (!lean_is_exclusive(v___x_6686_)) as u8;
                        if v_isSharedCheck_6717_ == 0 {
                            v___x_6712_ = v___x_6686_;
                            v_isShared_6713_ = v_isSharedCheck_6717_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6710_);
                            lean_dec(v___x_6686_);
                            v___x_6712_ = lean_box(0);
                            v_isShared_6713_ = v_isSharedCheck_6717_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if lean_obj_tag(v_a_6687_) == 1 {
                    lean_del_object(v___x_6689_);
                    v_options_6691_ = lean_ctor_get(v_a_6643_, 2);
                    v_hasTrace_6692_ = lean_ctor_get_uint8(
                        v_options_6691_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6692_ == 0 {
                        v_val_6693_ = lean_ctor_get(v_a_6687_, 0);
                        lean_inc(v_val_6693_);
                        lean_dec_ref_known(v_a_6687_, 1);
                        v___y_6656_ = v_val_6693_;
                        v___y_6657_ = v_a_6644_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6694_ = lean_ctor_get(v_a_6687_, 0);
                        lean_inc(v_val_6694_);
                        lean_dec_ref_known(v_a_6687_, 1);
                        v_inheritedTraceOptions_6695_ = lean_ctor_get(v_a_6643_, 13);
                        v___x_6696_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5;
                        v___x_6697_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__8_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__8);
                        v___x_6698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_6695_,
                            v_options_6691_,
                            v___x_6697_,
                        );
                        if v___x_6698_ == 0 {
                            v___y_6656_ = v_val_6694_;
                            v___y_6657_ = v_a_6644_;
                            state = 2;
                            continue;
                        } else {
                            v___x_6699_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__10_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__10);
                            lean_inc(v_name_6652_);
                            v___x_6700_ = l_Lean_MessageData_ofName(v_name_6652_);
                            v___x_6701_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6701_, 0, v___x_6699_);
                            lean_ctor_set(v___x_6701_, 1, v___x_6700_);
                            v___x_6702_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__12_once), _init_l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__12);
                            v___x_6703_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6703_, 0, v___x_6701_);
                            lean_ctor_set(v___x_6703_, 1, v___x_6702_);
                            v___x_6704_ = l_Lean_addTrace___at___00__private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround_spec__0(v___x_6696_, v___x_6703_, v_a_6641_, v_a_6642_, v_a_6643_, v_a_6644_);
                            if lean_obj_tag(v___x_6704_) == 0 {
                                lean_dec_ref_known(v___x_6704_, 1);
                                v___y_6656_ = v_val_6694_;
                                v___y_6657_ = v_a_6644_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_val_6694_);
                                lean_dec(v_name_6652_);
                                lean_del_object(v___x_6650_);
                                return v___x_6704_;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_6687_);
                    lean_dec(v_name_6652_);
                    lean_del_object(v___x_6650_);
                    v___x_6705_ = lean_box(0);
                    if v_isShared_6690_ == 0 {
                        lean_ctor_set(v___x_6689_, 0, v___x_6705_);
                        v___x_6707_ = v___x_6689_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6708_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6708_, 0, v___x_6705_);
                        v___x_6707_ = v_reuseFailAlloc_6708_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_6707_;
            }
            9 => {
                if v_isShared_6713_ == 0 {
                    v___x_6715_ = v___x_6712_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_a_6710_);
                    v___x_6715_ = v_reuseFailAlloc_6716_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___boxed(
    mut v_d_6725_: *mut LeanObject,
    mut v_a_6726_: *mut LeanObject,
    mut v_a_6727_: *mut LeanObject,
    mut v_a_6728_: *mut LeanObject,
    mut v_a_6729_: *mut LeanObject,
    mut v_a_6730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6731_: *mut LeanObject = core::ptr::null_mut();
    v_res_6731_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround(v_d_6725_, v_a_6726_, v_a_6727_, v_a_6728_, v_a_6729_);
    lean_dec(v_a_6729_);
    lean_dec_ref(v_a_6728_);
    lean_dec(v_a_6727_);
    lean_dec_ref(v_a_6726_);
    return v_res_6731_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_detectSimpleGround_spec__0(
    mut v_as_6732_: *mut LeanObject,
    mut v_i_6733_: usize,
    mut v_stop_6734_: usize,
    mut v_b_6735_: *mut LeanObject,
    mut v___y_6736_: *mut LeanObject,
    mut v___y_6737_: *mut LeanObject,
    mut v___y_6738_: *mut LeanObject,
    mut v___y_6739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6741_: u8 = 0;
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: usize = 0;
    let mut v___x_6746_: usize = 0;
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6741_ = lean_usize_dec_eq(v_i_6733_, v_stop_6734_);
                if v___x_6741_ == 0 {
                    v___x_6742_ = lean_array_uget_borrowed(v_as_6732_, v_i_6733_);
                    lean_inc(v___x_6742_);
                    v___x_6743_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround(v___x_6742_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_);
                    if lean_obj_tag(v___x_6743_) == 0 {
                        v_a_6744_ = lean_ctor_get(v___x_6743_, 0);
                        lean_inc(v_a_6744_);
                        lean_dec_ref_known(v___x_6743_, 1);
                        v___x_6745_ = 1usize;
                        v___x_6746_ = lean_usize_add(v_i_6733_, v___x_6745_);
                        v_i_6733_ = v___x_6746_;
                        v_b_6735_ = v_a_6744_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6743_;
                    }
                } else {
                    v___x_6748_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6748_, 0, v_b_6735_);
                    return v___x_6748_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_detectSimpleGround_spec__0___boxed(
    mut v_as_6749_: *mut LeanObject,
    mut v_i_6750_: *mut LeanObject,
    mut v_stop_6751_: *mut LeanObject,
    mut v_b_6752_: *mut LeanObject,
    mut v___y_6753_: *mut LeanObject,
    mut v___y_6754_: *mut LeanObject,
    mut v___y_6755_: *mut LeanObject,
    mut v___y_6756_: *mut LeanObject,
    mut v___y_6757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6758_: usize = 0;
    let mut v_stop_boxed_6759_: usize = 0;
    let mut v_res_6760_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6758_ = lean_unbox_usize(v_i_6750_);
    lean_dec(v_i_6750_);
    v_stop_boxed_6759_ = lean_unbox_usize(v_stop_6751_);
    lean_dec(v_stop_6751_);
    v_res_6760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_detectSimpleGround_spec__0(v_as_6749_, v_i_boxed_6758_, v_stop_boxed_6759_, v_b_6752_, v___y_6753_, v___y_6754_, v___y_6755_, v___y_6756_);
    lean_dec(v___y_6756_);
    lean_dec_ref(v___y_6755_);
    lean_dec(v___y_6754_);
    lean_dec_ref(v___y_6753_);
    lean_dec_ref(v_as_6749_);
    return v_res_6760_;
}
pub unsafe fn l_Lean_Compiler_LCNF_detectSimpleGround___lam__0(
    mut v___x_6761_: *mut LeanObject,
    mut v_decls_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
    mut v___y_6765_: *mut LeanObject,
    mut v___y_6766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6772_: u8 = 0;
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6776_: u8 = 0;
    let mut v_unused_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6781_: u8 = 0;
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6785_: u8 = 0;
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: u8 = 0;
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: u8 = 0;
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: usize = 0;
    let mut v___x_6793_: usize = 0;
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: usize = 0;
    let mut v___x_6796_: usize = 0;
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6786_ = lean_array_get_size(v_decls_6762_);
                v___x_6787_ = lean_nat_dec_lt(v___x_6761_, v___x_6786_);
                if v___x_6787_ == 0 {
                    v___x_6788_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6788_, 0, v_decls_6762_);
                    return v___x_6788_;
                } else {
                    v___x_6789_ = lean_box(0);
                    v___x_6790_ = lean_nat_dec_le(v___x_6786_, v___x_6786_);
                    if v___x_6790_ == 0 {
                        if v___x_6787_ == 0 {
                            v___x_6791_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_6791_, 0, v_decls_6762_);
                            return v___x_6791_;
                        } else {
                            v___x_6792_ = 0usize;
                            v___x_6793_ = lean_usize_of_nat(v___x_6786_);
                            v___x_6794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_detectSimpleGround_spec__0(v_decls_6762_, v___x_6792_, v___x_6793_, v___x_6789_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_);
                            v___y_6769_ = v___x_6794_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_6795_ = 0usize;
                        v___x_6796_ = lean_usize_of_nat(v___x_6786_);
                        v___x_6797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_detectSimpleGround_spec__0(v_decls_6762_, v___x_6795_, v___x_6796_, v___x_6789_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_);
                        v___y_6769_ = v___x_6797_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_6769_) == 0 {
                    v_isSharedCheck_6776_ = (!lean_is_exclusive(v___y_6769_)) as u8;
                    if v_isSharedCheck_6776_ == 0 {
                        v_unused_6777_ = lean_ctor_get(v___y_6769_, 0);
                        lean_dec(v_unused_6777_);
                        v___x_6771_ = v___y_6769_;
                        v_isShared_6772_ = v_isSharedCheck_6776_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___y_6769_);
                        v___x_6771_ = lean_box(0);
                        v_isShared_6772_ = v_isSharedCheck_6776_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decls_6762_);
                    v_a_6778_ = lean_ctor_get(v___y_6769_, 0);
                    v_isSharedCheck_6785_ = (!lean_is_exclusive(v___y_6769_)) as u8;
                    if v_isSharedCheck_6785_ == 0 {
                        v___x_6780_ = v___y_6769_;
                        v_isShared_6781_ = v_isSharedCheck_6785_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6778_);
                        lean_dec(v___y_6769_);
                        v___x_6780_ = lean_box(0);
                        v_isShared_6781_ = v_isSharedCheck_6785_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6772_ == 0 {
                    lean_ctor_set(v___x_6771_, 0, v_decls_6762_);
                    v___x_6774_ = v___x_6771_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6775_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6775_, 0, v_decls_6762_);
                    v___x_6774_ = v_reuseFailAlloc_6775_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6774_;
            }
            4 => {
                if v_isShared_6781_ == 0 {
                    v___x_6783_ = v___x_6780_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_a_6778_);
                    v___x_6783_ = v_reuseFailAlloc_6784_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_detectSimpleGround___lam__0___boxed(
    mut v___x_6798_: *mut LeanObject,
    mut v_decls_6799_: *mut LeanObject,
    mut v___y_6800_: *mut LeanObject,
    mut v___y_6801_: *mut LeanObject,
    mut v___y_6802_: *mut LeanObject,
    mut v___y_6803_: *mut LeanObject,
    mut v___y_6804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6805_: *mut LeanObject = core::ptr::null_mut();
    v_res_6805_ = l_Lean_Compiler_LCNF_detectSimpleGround___lam__0(
        v___x_6798_,
        v_decls_6799_,
        v___y_6800_,
        v___y_6801_,
        v___y_6802_,
        v___y_6803_,
    );
    lean_dec(v___y_6803_);
    lean_dec_ref(v___y_6802_);
    lean_dec(v___y_6801_);
    lean_dec_ref(v___y_6800_);
    lean_dec(v___x_6798_);
    return v_res_6805_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: u8 = 0;
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    v___x_6883_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_Decl_detectSimpleGround___closed__5;
    v___x_6884_ = 1;
    v___x_6885_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_;
    v___x_6886_ = l_Lean_registerTraceClass(v___x_6883_, v___x_6884_, v___x_6885_);
    return v___x_6886_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2____boxed(
    mut v_a_6887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6888_: *mut LeanObject = core::ptr::null_mut();
    v_res_6888_ = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_();
    return v_res_6888_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default();
    lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState_default);
    l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState =
        _init_l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState();
    lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedSimpleGroundExtState);
    res = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_160484116____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_simpleGroundDeclExt =
        lean_io_result_get_value(res);
    lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_simpleGroundDeclExt,
    );
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_SimpleGroundExpr_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_SimpleGroundExpr_1728217338____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin);
}
