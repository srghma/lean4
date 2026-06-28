// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: Lean.Compiler.IR.CompilerM Lean.Compiler.IR.ToIRType
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::IR::Basic::{
    l_Lean_IR_instInhabitedArg_default, l_Lean_IR_instInhabitedFnBody_default__1,
    l_Lean_IR_mkDummyExternDecl,
};
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, l_Lean_IR_declMapExt,
    runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Compiler::IR::ToIRType::{
    initialize_Lean_Compiler_IR_ToIRType, l_Lean_IR_nameToIRType, l_Lean_IR_toIRType,
    runtime_initialize_Lean_Compiler_IR_ToIRType,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::l_Lean_PersistentEnvExtension_addEntry___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_instBEqFVarId_beq, l_Lean_instHashableFVarId_hash};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint16_to_nat, lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_panic_fn_borrowed, lean_uint32_to_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_4,
    lean_apply_5, lean_box, lean_closure_set, lean_cstr_to_nat, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint16, lean_ctor_get_uint32, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_Lean_IR_ToIR_M_run___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_M_run___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_M_run___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_M_run___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_M_run___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_M_run___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 72, 97, 115, 104, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 65, 115, 115, 111, 99, 76, 105, 115, 116, 46, 103, 101, 116, 33, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 112, 114, 101, 115, 101, 110, 116, 32, 105, 110, 32, 104, 97, 115, 104, 32, 116, 97, 98, 108, 101, 0]};
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_addDecl___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_addDecl___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_addDecl___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_addDecl___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_addDecl___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_addDecl___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1_value)
        as *mut LeanObject;
pub static l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_IR_ToIR_lowerCode___closed__2_value: LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 38,
    m_data: [
        97, 108, 108, 32, 108, 111, 99, 97, 108, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115,
        32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 206, 187, 45, 108, 105, 102, 116, 101,
        100, 0,
    ],
};
static mut l_Lean_IR_ToIR_lowerCode___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_ToIR_lowerCode___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_ToIR_lowerCode___closed__1_value: LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 46, 73, 82, 46, 84, 111, 73, 82, 46, 108, 111, 119, 101, 114, 67, 111,
        100, 101, 0,
    ],
};
static mut l_Lean_IR_ToIR_lowerCode___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_ToIR_lowerCode___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_ToIR_lowerCode___closed__0_value: LeanStringObject<22> = LeanStringObject {
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
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 73, 82, 46, 84, 111, 73,
        82, 0,
    ],
};
static mut l_Lean_IR_ToIR_lowerCode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_ToIR_lowerCode___closed__0_value) as *mut LeanObject;
static mut l_Lean_IR_ToIR_lowerCode___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_ToIR_lowerCode___closed__4_value: LeanStringObject<34> = LeanStringObject {
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_IR_ToIR_lowerCode___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_ToIR_lowerCode___closed__4_value) as *mut LeanObject;
static mut l_Lean_IR_ToIR_lowerCode___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_ToIR_lowerCode___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_ToIR_lowerCode___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_toIR___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_IR_toIR___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_toIR___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_IR_ToIR_M_run___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    v___x_1922_ = lean_box(0);
    v___x_1923_ = lean_unsigned_to_nat(16);
    v___x_1924_ = lean_mk_array(v___x_1923_, v___x_1922_);
    return v___x_1924_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_M_run___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    v___x_1925_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_M_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_M_run___redArg___closed__0_once),
        _init_l_Lean_IR_ToIR_M_run___redArg___closed__0,
    );
    v___x_1926_ = lean_unsigned_to_nat(0);
    v___x_1927_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1927_, 0, v___x_1926_);
    lean_ctor_set(v___x_1927_, 1, v___x_1925_);
    return v___x_1927_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_M_run___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    v___x_1928_ = lean_unsigned_to_nat(1);
    v___x_1929_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_M_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_M_run___redArg___closed__1_once),
        _init_l_Lean_IR_ToIR_M_run___redArg___closed__1,
    );
    v___x_1930_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1930_, 0, v___x_1929_);
    lean_ctor_set(v___x_1930_, 1, v___x_1929_);
    lean_ctor_set(v___x_1930_, 2, v___x_1928_);
    return v___x_1930_;
}
pub unsafe fn l_Lean_IR_ToIR_M_run___redArg(
    mut v_x_1931_: *mut LeanObject,
    mut v_a_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1935_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_ToIR_M_run___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_IR_ToIR_M_run___redArg___closed__2_once),
                    _init_l_Lean_IR_ToIR_M_run___redArg___closed__2,
                );
                v___x_1936_ = lean_st_mk_ref(v___x_1935_);
                lean_inc(v_a_1933_);
                lean_inc_ref(v_a_1932_);
                lean_inc(v___x_1936_);
                v___x_1937_ =
                    lean_apply_4(v_x_1931_, v___x_1936_, v_a_1932_, v_a_1933_, lean_box(0));
                if lean_obj_tag(v___x_1937_) == 0 {
                    v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
                    v_isSharedCheck_1946_ = (!lean_is_exclusive(v___x_1937_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1940_ = v___x_1937_;
                        v_isShared_1941_ = v_isSharedCheck_1946_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1938_);
                        lean_dec(v___x_1937_);
                        v___x_1940_ = lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1946_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1936_);
                    return v___x_1937_;
                }
            }
            1 => {
                v___x_1942_ = lean_st_ref_get(v___x_1936_);
                lean_dec(v___x_1936_);
                lean_dec(v___x_1942_);
                if v_isShared_1941_ == 0 {
                    v___x_1944_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1938_);
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
pub unsafe fn l_Lean_IR_ToIR_M_run___redArg___boxed(
    mut v_x_1947_: *mut LeanObject,
    mut v_a_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1951_: *mut LeanObject = core::ptr::null_mut();
    v_res_1951_ = l_Lean_IR_ToIR_M_run___redArg(v_x_1947_, v_a_1948_, v_a_1949_);
    lean_dec(v_a_1949_);
    lean_dec_ref(v_a_1948_);
    return v_res_1951_;
}
pub unsafe fn l_Lean_IR_ToIR_M_run(
    mut v_00_u03b1_1952_: *mut LeanObject,
    mut v_x_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    v___x_1957_ = l_Lean_IR_ToIR_M_run___redArg(v_x_1953_, v_a_1954_, v_a_1955_);
    return v___x_1957_;
}
pub unsafe fn l_Lean_IR_ToIR_M_run___boxed(
    mut v_00_u03b1_1958_: *mut LeanObject,
    mut v_x_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
    mut v_a_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1963_: *mut LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_IR_ToIR_M_run(v_00_u03b1_1958_, v_x_1959_, v_a_1960_, v_a_1961_);
    lean_dec(v_a_1961_);
    lean_dec_ref(v_a_1960_);
    return v_res_1963_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(
    mut v_msg_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Lean_IR_instInhabitedArg_default;
    v___x_1966_ = lean_panic_fn_borrowed(v___x_1965_, v_msg_1964_);
    return v___x_1966_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__2;
    v___x_1971_ = lean_unsigned_to_nat(11);
    v___x_1972_ = lean_unsigned_to_nat(163);
    v___x_1973_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__1;
    v___x_1974_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__0;
    v___x_1975_ = l_mkPanicMessageWithDecl(
        v___x_1974_,
        v___x_1973_,
        v___x_1972_,
        v___x_1971_,
        v___x_1970_,
    );
    return v___x_1975_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(
    mut v_a_1976_: *mut LeanObject,
    mut v_x_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1977_) == 0 {
                    v___x_1978_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3);
                    v___x_1979_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(v___x_1978_);
                    return v___x_1979_;
                } else {
                    v_key_1980_ = lean_ctor_get(v_x_1977_, 0);
                    v_value_1981_ = lean_ctor_get(v_x_1977_, 1);
                    v_tail_1982_ = lean_ctor_get(v_x_1977_, 2);
                    v___x_1983_ = l_Lean_instBEqFVarId_beq(v_key_1980_, v_a_1976_);
                    if v___x_1983_ == 0 {
                        v_x_1977_ = v_tail_1982_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_1981_);
                        return v_value_1981_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(
    mut v_a_1985_: *mut LeanObject,
    mut v_x_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1987_: *mut LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_a_1985_, v_x_1986_);
    lean_dec(v_x_1986_);
    lean_dec(v_a_1985_);
    return v_res_1987_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(
    mut v_m_1988_: *mut LeanObject,
    mut v_a_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u64 = 0;
    let mut v___x_1993_: u64 = 0;
    let mut v___x_1994_: u64 = 0;
    let mut v_fold_1995_: u64 = 0;
    let mut v___x_1996_: u64 = 0;
    let mut v___x_1997_: u64 = 0;
    let mut v___x_1998_: u64 = 0;
    let mut v___x_1999_: usize = 0;
    let mut v___x_2000_: usize = 0;
    let mut v___x_2001_: usize = 0;
    let mut v___x_2002_: usize = 0;
    let mut v___x_2003_: usize = 0;
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_1990_ = lean_ctor_get(v_m_1988_, 1);
    v___x_1991_ = lean_array_get_size(v_buckets_1990_);
    v___x_1992_ = l_Lean_instHashableFVarId_hash(v_a_1989_);
    v___x_1993_ = 32u64;
    v___x_1994_ = lean_uint64_shift_right(v___x_1992_, v___x_1993_);
    v_fold_1995_ = lean_uint64_xor(v___x_1992_, v___x_1994_);
    v___x_1996_ = 16u64;
    v___x_1997_ = lean_uint64_shift_right(v_fold_1995_, v___x_1996_);
    v___x_1998_ = lean_uint64_xor(v_fold_1995_, v___x_1997_);
    v___x_1999_ = lean_uint64_to_usize(v___x_1998_);
    v___x_2000_ = lean_usize_of_nat(v___x_1991_);
    v___x_2001_ = 1usize;
    v___x_2002_ = lean_usize_sub(v___x_2000_, v___x_2001_);
    v___x_2003_ = lean_usize_land(v___x_1999_, v___x_2002_);
    v___x_2004_ = lean_array_uget_borrowed(v_buckets_1990_, v___x_2003_);
    v___x_2005_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(v_a_1989_, v___x_2004_);
    return v___x_2005_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(
    mut v_m_2006_: *mut LeanObject,
    mut v_a_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2008_: *mut LeanObject = core::ptr::null_mut();
    v_res_2008_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(
            v_m_2006_, v_a_2007_,
        );
    lean_dec(v_a_2007_);
    lean_dec_ref(v_m_2006_);
    return v_res_2008_;
}
pub unsafe fn l_Lean_IR_ToIR_getFVarValue___redArg(
    mut v_fvarId_2009_: *mut LeanObject,
    mut v_a_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    v___x_2012_ = lean_st_ref_get(v_a_2010_);
    v_vars_2013_ = lean_ctor_get(v___x_2012_, 0);
    lean_inc_ref(v_vars_2013_);
    lean_dec(v___x_2012_);
    v___x_2014_ =
        l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(
            v_vars_2013_,
            v_fvarId_2009_,
        );
    lean_dec_ref(v_vars_2013_);
    v___x_2015_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2015_, 0, v___x_2014_);
    return v___x_2015_;
}
pub unsafe fn l_Lean_IR_ToIR_getFVarValue___redArg___boxed(
    mut v_fvarId_2016_: *mut LeanObject,
    mut v_a_2017_: *mut LeanObject,
    mut v_a_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2019_: *mut LeanObject = core::ptr::null_mut();
    v_res_2019_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_2016_, v_a_2017_);
    lean_dec(v_a_2017_);
    lean_dec(v_fvarId_2016_);
    return v_res_2019_;
}
pub unsafe fn l_Lean_IR_ToIR_getFVarValue(
    mut v_fvarId_2020_: *mut LeanObject,
    mut v_a_2021_: *mut LeanObject,
    mut v_a_2022_: *mut LeanObject,
    mut v_a_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    v___x_2025_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_2020_, v_a_2021_);
    return v___x_2025_;
}
pub unsafe fn l_Lean_IR_ToIR_getFVarValue___boxed(
    mut v_fvarId_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
    mut v_a_2028_: *mut LeanObject,
    mut v_a_2029_: *mut LeanObject,
    mut v_a_2030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2031_: *mut LeanObject = core::ptr::null_mut();
    v_res_2031_ = l_Lean_IR_ToIR_getFVarValue(v_fvarId_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
    lean_dec(v_a_2029_);
    lean_dec_ref(v_a_2028_);
    lean_dec(v_a_2027_);
    lean_dec(v_fvarId_2026_);
    return v_res_2031_;
}
pub unsafe fn l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(
    mut v_msg_2032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    v___x_2033_ = lean_unsigned_to_nat(0);
    v___x_2034_ = lean_panic_fn_borrowed(v___x_2033_, v_msg_2032_);
    return v___x_2034_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(
    mut v_a_2035_: *mut LeanObject,
    mut v_x_2036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2036_) == 0 {
                    v___x_2037_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3_once), _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___closed__3);
                    v___x_2038_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0_spec__1(v___x_2037_);
                    return v___x_2038_;
                } else {
                    v_key_2039_ = lean_ctor_get(v_x_2036_, 0);
                    v_value_2040_ = lean_ctor_get(v_x_2036_, 1);
                    v_tail_2041_ = lean_ctor_get(v_x_2036_, 2);
                    v___x_2042_ = l_Lean_instBEqFVarId_beq(v_key_2039_, v_a_2035_);
                    if v___x_2042_ == 0 {
                        v_x_2036_ = v_tail_2041_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2040_);
                        return v_value_2040_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0___boxed(
    mut v_a_2044_: *mut LeanObject,
    mut v_x_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2046_: *mut LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(v_a_2044_, v_x_2045_);
    lean_dec(v_x_2045_);
    lean_dec(v_a_2044_);
    return v_res_2046_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(
    mut v_m_2047_: *mut LeanObject,
    mut v_a_2048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u64 = 0;
    let mut v___x_2052_: u64 = 0;
    let mut v___x_2053_: u64 = 0;
    let mut v_fold_2054_: u64 = 0;
    let mut v___x_2055_: u64 = 0;
    let mut v___x_2056_: u64 = 0;
    let mut v___x_2057_: u64 = 0;
    let mut v___x_2058_: usize = 0;
    let mut v___x_2059_: usize = 0;
    let mut v___x_2060_: usize = 0;
    let mut v___x_2061_: usize = 0;
    let mut v___x_2062_: usize = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2049_ = lean_ctor_get(v_m_2047_, 1);
    v___x_2050_ = lean_array_get_size(v_buckets_2049_);
    v___x_2051_ = l_Lean_instHashableFVarId_hash(v_a_2048_);
    v___x_2052_ = 32u64;
    v___x_2053_ = lean_uint64_shift_right(v___x_2051_, v___x_2052_);
    v_fold_2054_ = lean_uint64_xor(v___x_2051_, v___x_2053_);
    v___x_2055_ = 16u64;
    v___x_2056_ = lean_uint64_shift_right(v_fold_2054_, v___x_2055_);
    v___x_2057_ = lean_uint64_xor(v_fold_2054_, v___x_2056_);
    v___x_2058_ = lean_uint64_to_usize(v___x_2057_);
    v___x_2059_ = lean_usize_of_nat(v___x_2050_);
    v___x_2060_ = 1usize;
    v___x_2061_ = lean_usize_sub(v___x_2059_, v___x_2060_);
    v___x_2062_ = lean_usize_land(v___x_2058_, v___x_2061_);
    v___x_2063_ = lean_array_uget_borrowed(v_buckets_2049_, v___x_2062_);
    v___x_2064_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0_spec__0(v_a_2048_, v___x_2063_);
    return v___x_2064_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0___boxed(
    mut v_m_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2067_: *mut LeanObject = core::ptr::null_mut();
    v_res_2067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_m_2065_, v_a_2066_);
    lean_dec(v_a_2066_);
    lean_dec_ref(v_m_2065_);
    return v_res_2067_;
}
pub unsafe fn l_Lean_IR_ToIR_getJoinPointValue___redArg(
    mut v_fvarId_2068_: *mut LeanObject,
    mut v_a_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_joinPoints_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    v___x_2071_ = lean_st_ref_get(v_a_2069_);
    v_joinPoints_2072_ = lean_ctor_get(v___x_2071_, 1);
    lean_inc_ref(v_joinPoints_2072_);
    lean_dec(v___x_2071_);
    v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getJoinPointValue_spec__0(v_joinPoints_2072_, v_fvarId_2068_);
    lean_dec_ref(v_joinPoints_2072_);
    v___x_2074_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2074_, 0, v___x_2073_);
    return v___x_2074_;
}
pub unsafe fn l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(
    mut v_fvarId_2075_: *mut LeanObject,
    mut v_a_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2078_: *mut LeanObject = core::ptr::null_mut();
    v_res_2078_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_2075_, v_a_2076_);
    lean_dec(v_a_2076_);
    lean_dec(v_fvarId_2075_);
    return v_res_2078_;
}
pub unsafe fn l_Lean_IR_ToIR_getJoinPointValue(
    mut v_fvarId_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    v___x_2084_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_2079_, v_a_2080_);
    return v___x_2084_;
}
pub unsafe fn l_Lean_IR_ToIR_getJoinPointValue___boxed(
    mut v_fvarId_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2090_: *mut LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_IR_ToIR_getJoinPointValue(v_fvarId_2085_, v_a_2086_, v_a_2087_, v_a_2088_);
    lean_dec(v_a_2088_);
    lean_dec_ref(v_a_2087_);
    lean_dec(v_a_2086_);
    lean_dec(v_fvarId_2085_);
    return v_res_2090_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(
    mut v_a_2091_: *mut LeanObject,
    mut v_x_2092_: *mut LeanObject,
) -> u8 {
    let mut v___x_2093_: u8 = 0;
    let mut v_key_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2092_) == 0 {
                    v___x_2093_ = 0;
                    return v___x_2093_;
                } else {
                    v_key_2094_ = lean_ctor_get(v_x_2092_, 0);
                    v_tail_2095_ = lean_ctor_get(v_x_2092_, 2);
                    v___x_2096_ = l_Lean_instBEqFVarId_beq(v_key_2094_, v_a_2091_);
                    if v___x_2096_ == 0 {
                        v_x_2092_ = v_tail_2095_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2096_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(
    mut v_a_2098_: *mut LeanObject,
    mut v_x_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2100_: u8 = 0;
    let mut v_r_2101_: *mut LeanObject = core::ptr::null_mut();
    v_res_2100_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_2098_, v_x_2099_);
    lean_dec(v_x_2099_);
    lean_dec(v_a_2098_);
    v_r_2101_ = lean_box((v_res_2100_) as usize);
    return v_r_2101_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_2102_: *mut LeanObject,
    mut v_x_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: u64 = 0;
    let mut v___x_2112_: u64 = 0;
    let mut v___x_2113_: u64 = 0;
    let mut v_fold_2114_: u64 = 0;
    let mut v___x_2115_: u64 = 0;
    let mut v___x_2116_: u64 = 0;
    let mut v___x_2117_: u64 = 0;
    let mut v___x_2118_: usize = 0;
    let mut v___x_2119_: usize = 0;
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: usize = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2103_) == 0 {
                    return v_x_2102_;
                } else {
                    v_key_2104_ = lean_ctor_get(v_x_2103_, 0);
                    v_value_2105_ = lean_ctor_get(v_x_2103_, 1);
                    v_tail_2106_ = lean_ctor_get(v_x_2103_, 2);
                    v_isSharedCheck_2129_ = (!lean_is_exclusive(v_x_2103_)) as u8;
                    if v_isSharedCheck_2129_ == 0 {
                        v___x_2108_ = v_x_2103_;
                        v_isShared_2109_ = v_isSharedCheck_2129_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2106_);
                        lean_inc(v_value_2105_);
                        lean_inc(v_key_2104_);
                        lean_dec(v_x_2103_);
                        v___x_2108_ = lean_box(0);
                        v_isShared_2109_ = v_isSharedCheck_2129_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2110_ = lean_array_get_size(v_x_2102_);
                v___x_2111_ = l_Lean_instHashableFVarId_hash(v_key_2104_);
                v___x_2112_ = 32u64;
                v___x_2113_ = lean_uint64_shift_right(v___x_2111_, v___x_2112_);
                v_fold_2114_ = lean_uint64_xor(v___x_2111_, v___x_2113_);
                v___x_2115_ = 16u64;
                v___x_2116_ = lean_uint64_shift_right(v_fold_2114_, v___x_2115_);
                v___x_2117_ = lean_uint64_xor(v_fold_2114_, v___x_2116_);
                v___x_2118_ = lean_uint64_to_usize(v___x_2117_);
                v___x_2119_ = lean_usize_of_nat(v___x_2110_);
                v___x_2120_ = 1usize;
                v___x_2121_ = lean_usize_sub(v___x_2119_, v___x_2120_);
                v___x_2122_ = lean_usize_land(v___x_2118_, v___x_2121_);
                v___x_2123_ = lean_array_uget_borrowed(v_x_2102_, v___x_2122_);
                lean_inc(v___x_2123_);
                if v_isShared_2109_ == 0 {
                    lean_ctor_set(v___x_2108_, 2, v___x_2123_);
                    v___x_2125_ = v___x_2108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_key_2104_);
                    lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_value_2105_);
                    lean_ctor_set(v_reuseFailAlloc_2128_, 2, v___x_2123_);
                    v___x_2125_ = v_reuseFailAlloc_2128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2126_ = lean_array_uset(v_x_2102_, v___x_2122_, v___x_2125_);
                v_x_2102_ = v___x_2126_;
                v_x_2103_ = v_tail_2106_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(
    mut v_i_2130_: *mut LeanObject,
    mut v_source_2131_: *mut LeanObject,
    mut v_target_2132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v_es_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2133_ = lean_array_get_size(v_source_2131_);
                v___x_2134_ = lean_nat_dec_lt(v_i_2130_, v___x_2133_);
                if v___x_2134_ == 0 {
                    lean_dec_ref(v_source_2131_);
                    lean_dec(v_i_2130_);
                    return v_target_2132_;
                } else {
                    v_es_2135_ = lean_array_fget(v_source_2131_, v_i_2130_);
                    v___x_2136_ = lean_box(0);
                    v_source_2137_ = lean_array_fset(v_source_2131_, v_i_2130_, v___x_2136_);
                    v_target_2138_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_target_2132_, v_es_2135_);
                    v___x_2139_ = lean_unsigned_to_nat(1);
                    v___x_2140_ = lean_nat_add(v_i_2130_, v___x_2139_);
                    lean_dec(v_i_2130_);
                    v_i_2130_ = v___x_2140_;
                    v_source_2131_ = v_source_2137_;
                    v_target_2132_ = v_target_2138_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(
    mut v_data_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    v___x_2143_ = lean_array_get_size(v_data_2142_);
    v___x_2144_ = lean_unsigned_to_nat(2);
    v_nbuckets_2145_ = lean_nat_mul(v___x_2143_, v___x_2144_);
    v___x_2146_ = lean_unsigned_to_nat(0);
    v___x_2147_ = lean_box(0);
    v___x_2148_ = lean_mk_array(v_nbuckets_2145_, v___x_2147_);
    v___x_2149_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v___x_2146_, v_data_2142_, v___x_2148_);
    return v___x_2149_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(
    mut v_m_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_b_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: u64 = 0;
    let mut v___x_2157_: u64 = 0;
    let mut v___x_2158_: u64 = 0;
    let mut v_fold_2159_: u64 = 0;
    let mut v___x_2160_: u64 = 0;
    let mut v___x_2161_: u64 = 0;
    let mut v___x_2162_: u64 = 0;
    let mut v___x_2163_: usize = 0;
    let mut v___x_2164_: usize = 0;
    let mut v___x_2165_: usize = 0;
    let mut v___x_2166_: usize = 0;
    let mut v___x_2167_: usize = 0;
    let mut v_bkt_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: u8 = 0;
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    let mut v_val_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_unused_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2153_ = lean_ctor_get(v_m_2150_, 0);
                v_buckets_2154_ = lean_ctor_get(v_m_2150_, 1);
                v___x_2155_ = lean_array_get_size(v_buckets_2154_);
                v___x_2156_ = l_Lean_instHashableFVarId_hash(v_a_2151_);
                v___x_2157_ = 32u64;
                v___x_2158_ = lean_uint64_shift_right(v___x_2156_, v___x_2157_);
                v_fold_2159_ = lean_uint64_xor(v___x_2156_, v___x_2158_);
                v___x_2160_ = 16u64;
                v___x_2161_ = lean_uint64_shift_right(v_fold_2159_, v___x_2160_);
                v___x_2162_ = lean_uint64_xor(v_fold_2159_, v___x_2161_);
                v___x_2163_ = lean_uint64_to_usize(v___x_2162_);
                v___x_2164_ = lean_usize_of_nat(v___x_2155_);
                v___x_2165_ = 1usize;
                v___x_2166_ = lean_usize_sub(v___x_2164_, v___x_2165_);
                v___x_2167_ = lean_usize_land(v___x_2163_, v___x_2166_);
                v_bkt_2168_ = lean_array_uget_borrowed(v_buckets_2154_, v___x_2167_);
                v___x_2169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_2151_, v_bkt_2168_);
                if v___x_2169_ == 0 {
                    lean_inc_ref(v_buckets_2154_);
                    lean_inc(v_size_2153_);
                    v_isSharedCheck_2190_ = (!lean_is_exclusive(v_m_2150_)) as u8;
                    if v_isSharedCheck_2190_ == 0 {
                        v_unused_2191_ = lean_ctor_get(v_m_2150_, 1);
                        lean_dec(v_unused_2191_);
                        v_unused_2192_ = lean_ctor_get(v_m_2150_, 0);
                        lean_dec(v_unused_2192_);
                        v___x_2171_ = v_m_2150_;
                        v_isShared_2172_ = v_isSharedCheck_2190_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2150_);
                        v___x_2171_ = lean_box(0);
                        v_isShared_2172_ = v_isSharedCheck_2190_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2152_);
                    lean_dec(v_a_2151_);
                    return v_m_2150_;
                }
            }
            1 => {
                v___x_2173_ = lean_unsigned_to_nat(1);
                v_size_x27_2174_ = lean_nat_add(v_size_2153_, v___x_2173_);
                lean_dec(v_size_2153_);
                lean_inc(v_bkt_2168_);
                v___x_2175_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2175_, 0, v_a_2151_);
                lean_ctor_set(v___x_2175_, 1, v_b_2152_);
                lean_ctor_set(v___x_2175_, 2, v_bkt_2168_);
                v_buckets_x27_2176_ = lean_array_uset(v_buckets_2154_, v___x_2167_, v___x_2175_);
                v___x_2177_ = lean_unsigned_to_nat(4);
                v___x_2178_ = lean_nat_mul(v_size_x27_2174_, v___x_2177_);
                v___x_2179_ = lean_unsigned_to_nat(3);
                v___x_2180_ = lean_nat_div(v___x_2178_, v___x_2179_);
                lean_dec(v___x_2178_);
                v___x_2181_ = lean_array_get_size(v_buckets_x27_2176_);
                v___x_2182_ = lean_nat_dec_le(v___x_2180_, v___x_2181_);
                lean_dec(v___x_2180_);
                if v___x_2182_ == 0 {
                    v_val_2183_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_buckets_x27_2176_);
                    if v_isShared_2172_ == 0 {
                        lean_ctor_set(v___x_2171_, 1, v_val_2183_);
                        lean_ctor_set(v___x_2171_, 0, v_size_x27_2174_);
                        v___x_2185_ = v___x_2171_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_size_x27_2174_);
                        lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_val_2183_);
                        v___x_2185_ = v_reuseFailAlloc_2186_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2172_ == 0 {
                        lean_ctor_set(v___x_2171_, 1, v_buckets_x27_2176_);
                        lean_ctor_set(v___x_2171_, 0, v_size_x27_2174_);
                        v___x_2188_ = v___x_2171_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_size_x27_2174_);
                        lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_buckets_x27_2176_);
                        v___x_2188_ = v_reuseFailAlloc_2189_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2185_;
            }
            3 => {
                return v___x_2188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_bindVar___redArg(
    mut v_fvarId_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_joinPoints_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2196_ = lean_st_ref_take(v_a_2194_);
                v_vars_2197_ = lean_ctor_get(v___x_2196_, 0);
                v_joinPoints_2198_ = lean_ctor_get(v___x_2196_, 1);
                v_nextId_2199_ = lean_ctor_get(v___x_2196_, 2);
                v_isSharedCheck_2212_ = (!lean_is_exclusive(v___x_2196_)) as u8;
                if v_isSharedCheck_2212_ == 0 {
                    v___x_2201_ = v___x_2196_;
                    v_isShared_2202_ = v_isSharedCheck_2212_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextId_2199_);
                    lean_inc(v_joinPoints_2198_);
                    lean_inc(v_vars_2197_);
                    lean_dec(v___x_2196_);
                    v___x_2201_ = lean_box(0);
                    v_isShared_2202_ = v_isSharedCheck_2212_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_nextId_2199_);
                v___x_2203_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2203_, 0, v_nextId_2199_);
                v___x_2204_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_2197_, v_fvarId_2193_, v___x_2203_);
                v___x_2205_ = lean_unsigned_to_nat(1);
                v___x_2206_ = lean_nat_add(v_nextId_2199_, v___x_2205_);
                if v_isShared_2202_ == 0 {
                    lean_ctor_set(v___x_2201_, 2, v___x_2206_);
                    lean_ctor_set(v___x_2201_, 0, v___x_2204_);
                    v___x_2208_ = v___x_2201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2204_);
                    lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_joinPoints_2198_);
                    lean_ctor_set(v_reuseFailAlloc_2211_, 2, v___x_2206_);
                    v___x_2208_ = v_reuseFailAlloc_2211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2209_ = lean_st_ref_set(v_a_2194_, v___x_2208_);
                v___x_2210_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2210_, 0, v_nextId_2199_);
                return v___x_2210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_bindVar___redArg___boxed(
    mut v_fvarId_2213_: *mut LeanObject,
    mut v_a_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2216_: *mut LeanObject = core::ptr::null_mut();
    v_res_2216_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_2213_, v_a_2214_);
    lean_dec(v_a_2214_);
    return v_res_2216_;
}
pub unsafe fn l_Lean_IR_ToIR_bindVar(
    mut v_fvarId_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
    mut v_a_2219_: *mut LeanObject,
    mut v_a_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    v___x_2222_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_2217_, v_a_2218_);
    return v___x_2222_;
}
pub unsafe fn l_Lean_IR_ToIR_bindVar___boxed(
    mut v_fvarId_2223_: *mut LeanObject,
    mut v_a_2224_: *mut LeanObject,
    mut v_a_2225_: *mut LeanObject,
    mut v_a_2226_: *mut LeanObject,
    mut v_a_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2228_: *mut LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_IR_ToIR_bindVar(v_fvarId_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
    lean_dec(v_a_2226_);
    lean_dec_ref(v_a_2225_);
    lean_dec(v_a_2224_);
    return v_res_2228_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(
    mut v_00_u03b2_2229_: *mut LeanObject,
    mut v_m_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
    mut v_b_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    v___x_2233_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_m_2230_, v_a_2231_, v_b_2232_);
    return v___x_2233_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(
    mut v_00_u03b2_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_x_2236_: *mut LeanObject,
) -> u8 {
    let mut v___x_2237_: u8 = 0;
    v___x_2237_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(v_a_2235_, v_x_2236_);
    return v___x_2237_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
    mut v_x_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2241_: u8 = 0;
    let mut v_r_2242_: *mut LeanObject = core::ptr::null_mut();
    v_res_2241_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(v_00_u03b2_2238_, v_a_2239_, v_x_2240_);
    lean_dec(v_x_2240_);
    lean_dec(v_a_2239_);
    v_r_2242_ = lean_box((v_res_2241_) as usize);
    return v_r_2242_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(
    mut v_00_u03b2_2243_: *mut LeanObject,
    mut v_data_2244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(v_data_2244_);
    return v___x_2245_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(
    mut v_00_u03b2_2246_: *mut LeanObject,
    mut v_i_2247_: *mut LeanObject,
    mut v_source_2248_: *mut LeanObject,
    mut v_target_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(v_i_2247_, v_source_2248_, v_target_2249_);
    return v___x_2250_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2251_: *mut LeanObject,
    mut v_x_2252_: *mut LeanObject,
    mut v_x_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    v___x_2254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(v_x_2252_, v_x_2253_);
    return v___x_2254_;
}
pub unsafe fn l_Lean_IR_ToIR_bindJoinPoint___redArg(
    mut v_fvarId_2255_: *mut LeanObject,
    mut v_a_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_joinPoints_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2258_ = lean_st_ref_take(v_a_2256_);
                v_vars_2259_ = lean_ctor_get(v___x_2258_, 0);
                v_joinPoints_2260_ = lean_ctor_get(v___x_2258_, 1);
                v_nextId_2261_ = lean_ctor_get(v___x_2258_, 2);
                v_isSharedCheck_2273_ = (!lean_is_exclusive(v___x_2258_)) as u8;
                if v_isSharedCheck_2273_ == 0 {
                    v___x_2263_ = v___x_2258_;
                    v_isShared_2264_ = v_isSharedCheck_2273_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextId_2261_);
                    lean_inc(v_joinPoints_2260_);
                    lean_inc(v_vars_2259_);
                    lean_dec(v___x_2258_);
                    v___x_2263_ = lean_box(0);
                    v_isShared_2264_ = v_isSharedCheck_2273_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_nextId_2261_);
                v___x_2265_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_joinPoints_2260_, v_fvarId_2255_, v_nextId_2261_);
                v___x_2266_ = lean_unsigned_to_nat(1);
                v___x_2267_ = lean_nat_add(v_nextId_2261_, v___x_2266_);
                if v_isShared_2264_ == 0 {
                    lean_ctor_set(v___x_2263_, 2, v___x_2267_);
                    lean_ctor_set(v___x_2263_, 1, v___x_2265_);
                    v___x_2269_ = v___x_2263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_vars_2259_);
                    lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2265_);
                    lean_ctor_set(v_reuseFailAlloc_2272_, 2, v___x_2267_);
                    v___x_2269_ = v_reuseFailAlloc_2272_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2270_ = lean_st_ref_set(v_a_2256_, v___x_2269_);
                v___x_2271_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2271_, 0, v_nextId_2261_);
                return v___x_2271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(
    mut v_fvarId_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2277_: *mut LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_2274_, v_a_2275_);
    lean_dec(v_a_2275_);
    return v_res_2277_;
}
pub unsafe fn l_Lean_IR_ToIR_bindJoinPoint(
    mut v_fvarId_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    v___x_2283_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_2278_, v_a_2279_);
    return v___x_2283_;
}
pub unsafe fn l_Lean_IR_ToIR_bindJoinPoint___boxed(
    mut v_fvarId_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2289_: *mut LeanObject = core::ptr::null_mut();
    v_res_2289_ = l_Lean_IR_ToIR_bindJoinPoint(v_fvarId_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
    lean_dec(v_a_2287_);
    lean_dec_ref(v_a_2286_);
    lean_dec(v_a_2285_);
    return v_res_2289_;
}
pub unsafe fn l_Lean_IR_ToIR_bindErased___redArg(
    mut v_fvarId_2290_: *mut LeanObject,
    mut v_a_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_joinPoints_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextId_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2293_ = lean_st_ref_take(v_a_2291_);
                v_vars_2294_ = lean_ctor_get(v___x_2293_, 0);
                v_joinPoints_2295_ = lean_ctor_get(v___x_2293_, 1);
                v_nextId_2296_ = lean_ctor_get(v___x_2293_, 2);
                v_isSharedCheck_2308_ = (!lean_is_exclusive(v___x_2293_)) as u8;
                if v_isSharedCheck_2308_ == 0 {
                    v___x_2298_ = v___x_2293_;
                    v_isShared_2299_ = v_isSharedCheck_2308_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nextId_2296_);
                    lean_inc(v_joinPoints_2295_);
                    lean_inc(v_vars_2294_);
                    lean_dec(v___x_2293_);
                    v___x_2298_ = lean_box(0);
                    v_isShared_2299_ = v_isSharedCheck_2308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2300_ = lean_box(1);
                v___x_2301_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(v_vars_2294_, v_fvarId_2290_, v___x_2300_);
                if v_isShared_2299_ == 0 {
                    lean_ctor_set(v___x_2298_, 0, v___x_2301_);
                    v___x_2303_ = v___x_2298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_joinPoints_2295_);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_nextId_2296_);
                    v___x_2303_ = v_reuseFailAlloc_2307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2304_ = lean_st_ref_set(v_a_2291_, v___x_2303_);
                v___x_2305_ = lean_box(0);
                v___x_2306_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2306_, 0, v___x_2305_);
                return v___x_2306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_bindErased___redArg___boxed(
    mut v_fvarId_2309_: *mut LeanObject,
    mut v_a_2310_: *mut LeanObject,
    mut v_a_2311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2312_: *mut LeanObject = core::ptr::null_mut();
    v_res_2312_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_2309_, v_a_2310_);
    lean_dec(v_a_2310_);
    return v_res_2312_;
}
pub unsafe fn l_Lean_IR_ToIR_bindErased(
    mut v_fvarId_2313_: *mut LeanObject,
    mut v_a_2314_: *mut LeanObject,
    mut v_a_2315_: *mut LeanObject,
    mut v_a_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    v___x_2318_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_2313_, v_a_2314_);
    return v___x_2318_;
}
pub unsafe fn l_Lean_IR_ToIR_bindErased___boxed(
    mut v_fvarId_2319_: *mut LeanObject,
    mut v_a_2320_: *mut LeanObject,
    mut v_a_2321_: *mut LeanObject,
    mut v_a_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2324_: *mut LeanObject = core::ptr::null_mut();
    v_res_2324_ = l_Lean_IR_ToIR_bindErased(v_fvarId_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
    lean_dec(v_a_2322_);
    lean_dec_ref(v_a_2321_);
    lean_dec(v_a_2320_);
    return v_res_2324_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    v___x_2325_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2325_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    v___x_2326_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_addDecl___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_addDecl___redArg___closed__0_once),
        _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0,
    );
    v___x_2327_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2327_, 0, v___x_2326_);
    return v___x_2327_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    v___x_2328_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_addDecl___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_addDecl___redArg___closed__1_once),
        _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1,
    );
    v___x_2329_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2329_, 0, v___x_2328_);
    lean_ctor_set(v___x_2329_, 1, v___x_2328_);
    return v___x_2329_;
}
pub unsafe fn l_Lean_IR_ToIR_addDecl___redArg(
    mut v_d_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v_unused_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2333_ = lean_st_ref_take(v_a_2331_);
                v_env_2334_ = lean_ctor_get(v___x_2333_, 0);
                v_nextMacroScope_2335_ = lean_ctor_get(v___x_2333_, 1);
                v_ngen_2336_ = lean_ctor_get(v___x_2333_, 2);
                v_auxDeclNGen_2337_ = lean_ctor_get(v___x_2333_, 3);
                v_traceState_2338_ = lean_ctor_get(v___x_2333_, 4);
                v_messages_2339_ = lean_ctor_get(v___x_2333_, 6);
                v_infoState_2340_ = lean_ctor_get(v___x_2333_, 7);
                v_snapshotTasks_2341_ = lean_ctor_get(v___x_2333_, 8);
                v_isSharedCheck_2357_ = (!lean_is_exclusive(v___x_2333_)) as u8;
                if v_isSharedCheck_2357_ == 0 {
                    v_unused_2358_ = lean_ctor_get(v___x_2333_, 5);
                    lean_dec(v_unused_2358_);
                    v___x_2343_ = v___x_2333_;
                    v_isShared_2344_ = v_isSharedCheck_2357_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2341_);
                    lean_inc(v_infoState_2340_);
                    lean_inc(v_messages_2339_);
                    lean_inc(v_traceState_2338_);
                    lean_inc(v_auxDeclNGen_2337_);
                    lean_inc(v_ngen_2336_);
                    lean_inc(v_nextMacroScope_2335_);
                    lean_inc(v_env_2334_);
                    lean_dec(v___x_2333_);
                    v___x_2343_ = lean_box(0);
                    v_isShared_2344_ = v_isSharedCheck_2357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2345_ = l_Lean_IR_declMapExt;
                v_toEnvExtension_2346_ = lean_ctor_get(v___x_2345_, 0);
                v_asyncMode_2347_ = lean_ctor_get(v_toEnvExtension_2346_, 2);
                v___x_2348_ = lean_box(0);
                v___x_2349_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2345_,
                    v_env_2334_,
                    v_d_2330_,
                    v_asyncMode_2347_,
                    v___x_2348_,
                );
                v___x_2350_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_IR_ToIR_addDecl___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_IR_ToIR_addDecl___redArg___closed__2_once),
                    _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2,
                );
                if v_isShared_2344_ == 0 {
                    lean_ctor_set(v___x_2343_, 5, v___x_2350_);
                    lean_ctor_set(v___x_2343_, 0, v___x_2349_);
                    v___x_2352_ = v___x_2343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2349_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_nextMacroScope_2335_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 2, v_ngen_2336_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 3, v_auxDeclNGen_2337_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 4, v_traceState_2338_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 5, v___x_2350_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 6, v_messages_2339_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 7, v_infoState_2340_);
                    lean_ctor_set(v_reuseFailAlloc_2356_, 8, v_snapshotTasks_2341_);
                    v___x_2352_ = v_reuseFailAlloc_2356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2353_ = lean_st_ref_set(v_a_2331_, v___x_2352_);
                v___x_2354_ = lean_box(0);
                v___x_2355_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2355_, 0, v___x_2354_);
                return v___x_2355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_addDecl___redArg___boxed(
    mut v_d_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_a_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2362_: *mut LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_2359_, v_a_2360_);
    lean_dec(v_a_2360_);
    return v_res_2362_;
}
pub unsafe fn l_Lean_IR_ToIR_addDecl(
    mut v_d_2363_: *mut LeanObject,
    mut v_a_2364_: *mut LeanObject,
    mut v_a_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    v___x_2368_ = l_Lean_IR_ToIR_addDecl___redArg(v_d_2363_, v_a_2366_);
    return v___x_2368_;
}
pub unsafe fn l_Lean_IR_ToIR_addDecl___boxed(
    mut v_d_2369_: *mut LeanObject,
    mut v_a_2370_: *mut LeanObject,
    mut v_a_2371_: *mut LeanObject,
    mut v_a_2372_: *mut LeanObject,
    mut v_a_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2374_: *mut LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_Lean_IR_ToIR_addDecl(v_d_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
    lean_dec(v_a_2372_);
    lean_dec_ref(v_a_2371_);
    lean_dec(v_a_2370_);
    return v_res_2374_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLitValue(mut v_v_2375_: *mut LeanObject) -> *mut LeanObject {
    let mut v_val_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___y_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2390_: u8 = 0;
    let mut v_val_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2394_: u8 = 0;
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut v_val_2401_: u8 = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2406_: u16 = 0;
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2411_: u32 = 0;
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2416_: u64 = 0;
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2421_: u64 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_v_2375_) {
                0 => {
                    v_val_2376_ = lean_ctor_get(v_v_2375_, 0);
                    v_isSharedCheck_2390_ = (!lean_is_exclusive(v_v_2375_)) as u8;
                    if v_isSharedCheck_2390_ == 0 {
                        v___x_2378_ = v_v_2375_;
                        v_isShared_2379_ = v_isSharedCheck_2390_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2376_);
                        lean_dec(v_v_2375_);
                        v___x_2378_ = lean_box(0);
                        v_isShared_2379_ = v_isSharedCheck_2390_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_val_2391_ = lean_ctor_get(v_v_2375_, 0);
                    v_isSharedCheck_2400_ = (!lean_is_exclusive(v_v_2375_)) as u8;
                    if v_isSharedCheck_2400_ == 0 {
                        v___x_2393_ = v_v_2375_;
                        v_isShared_2394_ = v_isSharedCheck_2400_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_2391_);
                        lean_dec(v_v_2375_);
                        v___x_2393_ = lean_box(0);
                        v_isShared_2394_ = v_isSharedCheck_2400_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_val_2401_ = lean_ctor_get_uint8(v_v_2375_, 0 as u32);
                    lean_dec_ref_known(v_v_2375_, 0);
                    v___x_2402_ = lean_uint8_to_nat(v_val_2401_);
                    v___x_2403_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2403_, 0, v___x_2402_);
                    v___x_2404_ = lean_box(1);
                    v___x_2405_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2405_, 0, v___x_2403_);
                    lean_ctor_set(v___x_2405_, 1, v___x_2404_);
                    return v___x_2405_;
                }
                3 => {
                    v_val_2406_ = lean_ctor_get_uint16(v_v_2375_, 0 as u32);
                    lean_dec_ref_known(v_v_2375_, 0);
                    v___x_2407_ = lean_uint16_to_nat(v_val_2406_);
                    v___x_2408_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2408_, 0, v___x_2407_);
                    v___x_2409_ = lean_box(2);
                    v___x_2410_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2410_, 0, v___x_2408_);
                    lean_ctor_set(v___x_2410_, 1, v___x_2409_);
                    return v___x_2410_;
                }
                4 => {
                    v_val_2411_ = lean_ctor_get_uint32(v_v_2375_, 0 as u32);
                    lean_dec_ref_known(v_v_2375_, 0);
                    v___x_2412_ = lean_uint32_to_nat(v_val_2411_);
                    v___x_2413_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2413_, 0, v___x_2412_);
                    v___x_2414_ = lean_box(3);
                    v___x_2415_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2415_, 0, v___x_2413_);
                    lean_ctor_set(v___x_2415_, 1, v___x_2414_);
                    return v___x_2415_;
                }
                5 => {
                    v_val_2416_ = lean_ctor_get_uint64(v_v_2375_, 0 as u32);
                    lean_dec_ref_known(v_v_2375_, 0);
                    v___x_2417_ = lean_uint64_to_nat(v_val_2416_);
                    v___x_2418_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2418_, 0, v___x_2417_);
                    v___x_2419_ = lean_box(4);
                    v___x_2420_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2420_, 0, v___x_2418_);
                    lean_ctor_set(v___x_2420_, 1, v___x_2419_);
                    return v___x_2420_;
                }
                _ => {
                    v_val_2421_ = lean_ctor_get_uint64(v_v_2375_, 0 as u32);
                    lean_dec_ref_known(v_v_2375_, 0);
                    v___x_2422_ = lean_uint64_to_nat(v_val_2421_);
                    v___x_2423_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2423_, 0, v___x_2422_);
                    v___x_2424_ = lean_box(5);
                    v___x_2425_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2425_, 0, v___x_2423_);
                    lean_ctor_set(v___x_2425_, 1, v___x_2424_);
                    return v___x_2425_;
                }
            },
            1 => {
                v___x_2386_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
                v___x_2387_ = lean_nat_dec_lt(v_val_2376_, v___x_2386_);
                if v___x_2387_ == 0 {
                    v___x_2388_ = lean_box(8);
                    v___y_2381_ = v___x_2388_;
                    state = 2;
                    continue;
                } else {
                    v___x_2389_ = lean_box(12);
                    v___y_2381_ = v___x_2389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2379_ == 0 {
                    v___x_2383_ = v___x_2378_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_val_2376_);
                    v___x_2383_ = v_reuseFailAlloc_2385_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v___y_2381_);
                v___x_2384_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2384_, 0, v___x_2383_);
                lean_ctor_set(v___x_2384_, 1, v___y_2381_);
                return v___x_2384_;
            }
            4 => {
                if v_isShared_2394_ == 0 {
                    v___x_2396_ = v___x_2393_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_val_2391_);
                    v___x_2396_ = v_reuseFailAlloc_2399_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2397_ = lean_box(7);
                v___x_2398_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2398_, 0, v___x_2396_);
                lean_ctor_set(v___x_2398_, 1, v___x_2397_);
                return v___x_2398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerArg___redArg(
    mut v_a_2426_: *mut LeanObject,
    mut v_a_2427_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_2426_) == 0 {
        let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
        v___x_2429_ = lean_box(1);
        v___x_2430_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2430_, 0, v___x_2429_);
        return v___x_2430_;
    } else {
        let mut v_fvarId_2431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_2431_ = lean_ctor_get(v_a_2426_, 0);
        v___x_2432_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_2431_, v_a_2427_);
        return v___x_2432_;
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerArg___redArg___boxed(
    mut v_a_2433_: *mut LeanObject,
    mut v_a_2434_: *mut LeanObject,
    mut v_a_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_2433_, v_a_2434_);
    lean_dec(v_a_2434_);
    lean_dec(v_a_2433_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerArg(
    mut v_a_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    v___x_2442_ = l_Lean_IR_ToIR_lowerArg___redArg(v_a_2437_, v_a_2438_);
    return v___x_2442_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerArg___boxed(
    mut v_a_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2448_: *mut LeanObject = core::ptr::null_mut();
    v_res_2448_ = l_Lean_IR_ToIR_lowerArg(v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
    lean_dec(v_a_2446_);
    lean_dec_ref(v_a_2445_);
    lean_dec(v_a_2444_);
    lean_dec(v_a_2443_);
    return v_res_2448_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerParam___redArg(
    mut v_p_2449_: *mut LeanObject,
    mut v_a_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_2454_: u8 = 0;
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2459_: u8 = 0;
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_2452_ = lean_ctor_get(v_p_2449_, 0);
                lean_inc(v_fvarId_2452_);
                v_type_2453_ = lean_ctor_get(v_p_2449_, 2);
                lean_inc_ref(v_type_2453_);
                v_borrow_2454_ = lean_ctor_get_uint8(
                    v_p_2449_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_p_2449_);
                v___x_2455_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_2452_, v_a_2450_);
                v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
                v_isSharedCheck_2465_ = (!lean_is_exclusive(v___x_2455_)) as u8;
                if v_isSharedCheck_2465_ == 0 {
                    v___x_2458_ = v___x_2455_;
                    v_isShared_2459_ = v_isSharedCheck_2465_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2456_);
                    lean_dec(v___x_2455_);
                    v___x_2458_ = lean_box(0);
                    v_isShared_2459_ = v_isSharedCheck_2465_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2460_ = l_Lean_IR_toIRType(v_type_2453_);
                lean_dec_ref(v_type_2453_);
                v___x_2461_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2461_, 0, v_a_2456_);
                lean_ctor_set(v___x_2461_, 1, v___x_2460_);
                lean_ctor_set_uint8(
                    v___x_2461_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_borrow_2454_,
                );
                if v_isShared_2459_ == 0 {
                    lean_ctor_set(v___x_2458_, 0, v___x_2461_);
                    v___x_2463_ = v___x_2458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2461_);
                    v___x_2463_ = v_reuseFailAlloc_2464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerParam___redArg___boxed(
    mut v_p_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2469_: *mut LeanObject = core::ptr::null_mut();
    v_res_2469_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_2466_, v_a_2467_);
    lean_dec(v_a_2467_);
    return v_res_2469_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerParam(
    mut v_p_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
    mut v_a_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Lean_IR_ToIR_lowerParam___redArg(v_p_2470_, v_a_2471_);
    return v___x_2475_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerParam___boxed(
    mut v_p_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
    mut v_a_2478_: *mut LeanObject,
    mut v_a_2479_: *mut LeanObject,
    mut v_a_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_Lean_IR_ToIR_lowerParam(v_p_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
    lean_dec(v_a_2479_);
    lean_dec_ref(v_a_2478_);
    lean_dec(v_a_2477_);
    return v_res_2481_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerCtorInfo(mut v_i_2482_: *mut LeanObject) -> *mut LeanObject {
    let mut v_name_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_2483_ = lean_ctor_get(v_i_2482_, 0);
                v_cidx_2484_ = lean_ctor_get(v_i_2482_, 1);
                v_size_2485_ = lean_ctor_get(v_i_2482_, 2);
                v_usize_2486_ = lean_ctor_get(v_i_2482_, 3);
                v_ssize_2487_ = lean_ctor_get(v_i_2482_, 4);
                v_isSharedCheck_2494_ = (!lean_is_exclusive(v_i_2482_)) as u8;
                if v_isSharedCheck_2494_ == 0 {
                    v___x_2489_ = v_i_2482_;
                    v_isShared_2490_ = v_isSharedCheck_2494_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ssize_2487_);
                    lean_inc(v_usize_2486_);
                    lean_inc(v_size_2485_);
                    lean_inc(v_cidx_2484_);
                    lean_inc(v_name_2483_);
                    lean_dec(v_i_2482_);
                    v___x_2489_ = lean_box(0);
                    v_isShared_2490_ = v_isSharedCheck_2494_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2490_ == 0 {
                    v___x_2492_ = v___x_2489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_name_2483_);
                    lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_cidx_2484_);
                    lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_size_2485_);
                    lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_usize_2486_);
                    lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_ssize_2487_);
                    v___x_2492_ = v_reuseFailAlloc_2493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0() -> *mut LeanObject
{
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    v___x_2495_ = l_instMonadEIO(lean_box(0));
    return v___x_2495_;
}
pub unsafe fn l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
    mut v_msg_2498_: *mut LeanObject,
    mut v___y_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2508_: u8 = 0;
    let mut v_toFunctor_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2515_: u8 = 0;
    let mut v___f_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8618__overap_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut v_unused_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v_unused_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2503_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0_once
                    ),
                    _init_l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__0,
                );
                v___x_2504_ = l_StateRefT_x27_instMonad___redArg(v___x_2503_);
                v_toApplicative_2505_ = lean_ctor_get(v___x_2504_, 0);
                v_isSharedCheck_2537_ = (!lean_is_exclusive(v___x_2504_)) as u8;
                if v_isSharedCheck_2537_ == 0 {
                    v_unused_2538_ = lean_ctor_get(v___x_2504_, 1);
                    lean_dec(v_unused_2538_);
                    v___x_2507_ = v___x_2504_;
                    v_isShared_2508_ = v_isSharedCheck_2537_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2505_);
                    lean_dec(v___x_2504_);
                    v___x_2507_ = lean_box(0);
                    v_isShared_2508_ = v_isSharedCheck_2537_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2509_ = lean_ctor_get(v_toApplicative_2505_, 0);
                v_toSeq_2510_ = lean_ctor_get(v_toApplicative_2505_, 2);
                v_toSeqLeft_2511_ = lean_ctor_get(v_toApplicative_2505_, 3);
                v_toSeqRight_2512_ = lean_ctor_get(v_toApplicative_2505_, 4);
                v_isSharedCheck_2535_ = (!lean_is_exclusive(v_toApplicative_2505_)) as u8;
                if v_isSharedCheck_2535_ == 0 {
                    v_unused_2536_ = lean_ctor_get(v_toApplicative_2505_, 1);
                    lean_dec(v_unused_2536_);
                    v___x_2514_ = v_toApplicative_2505_;
                    v_isShared_2515_ = v_isSharedCheck_2535_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2512_);
                    lean_inc(v_toSeqLeft_2511_);
                    lean_inc(v_toSeq_2510_);
                    lean_inc(v_toFunctor_2509_);
                    lean_dec(v_toApplicative_2505_);
                    v___x_2514_ = lean_box(0);
                    v_isShared_2515_ = v_isSharedCheck_2535_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2516_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__1;
                v___f_2517_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___closed__2;
                lean_inc_ref(v_toFunctor_2509_);
                v___f_2518_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2518_, 0, v_toFunctor_2509_);
                v___f_2519_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2519_, 0, v_toFunctor_2509_);
                v___x_2520_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2520_, 0, v___f_2518_);
                lean_ctor_set(v___x_2520_, 1, v___f_2519_);
                v___f_2521_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2521_, 0, v_toSeqRight_2512_);
                v___f_2522_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2522_, 0, v_toSeqLeft_2511_);
                v___f_2523_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2523_, 0, v_toSeq_2510_);
                if v_isShared_2515_ == 0 {
                    lean_ctor_set(v___x_2514_, 4, v___f_2521_);
                    lean_ctor_set(v___x_2514_, 3, v___f_2522_);
                    lean_ctor_set(v___x_2514_, 2, v___f_2523_);
                    lean_ctor_set(v___x_2514_, 1, v___f_2516_);
                    lean_ctor_set(v___x_2514_, 0, v___x_2520_);
                    v___x_2525_ = v___x_2514_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2520_);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___f_2516_);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 2, v___f_2523_);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 3, v___f_2522_);
                    lean_ctor_set(v_reuseFailAlloc_2534_, 4, v___f_2521_);
                    v___x_2525_ = v_reuseFailAlloc_2534_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2508_ == 0 {
                    lean_ctor_set(v___x_2507_, 1, v___f_2517_);
                    lean_ctor_set(v___x_2507_, 0, v___x_2525_);
                    v___x_2527_ = v___x_2507_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2525_);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___f_2517_);
                    v___x_2527_ = v_reuseFailAlloc_2533_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2528_ = l_StateRefT_x27_instMonad___redArg(v___x_2527_);
                v___x_2529_ = l_Lean_IR_instInhabitedFnBody_default__1;
                v___x_2530_ = l_instInhabitedOfMonad___redArg(v___x_2528_, v___x_2529_);
                v___x_8618__overap_2531_ = lean_panic_fn_borrowed(v___x_2530_, v_msg_2498_);
                lean_dec(v___x_2530_);
                lean_inc(v___y_2501_);
                lean_inc_ref(v___y_2500_);
                lean_inc(v___y_2499_);
                v___x_2532_ = lean_apply_4(
                    v___x_8618__overap_2531_,
                    v___y_2499_,
                    v___y_2500_,
                    v___y_2501_,
                    lean_box(0),
                );
                return v___x_2532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1___boxed(
    mut v_msg_2539_: *mut LeanObject,
    mut v___y_2540_: *mut LeanObject,
    mut v___y_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
    mut v___y_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2544_: *mut LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
        v_msg_2539_,
        v___y_2540_,
        v___y_2541_,
        v___y_2542_,
    );
    lean_dec(v___y_2542_);
    lean_dec_ref(v___y_2541_);
    lean_dec(v___y_2540_);
    return v_res_2544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(
    mut v_sz_2545_: usize,
    mut v_i_2546_: usize,
    mut v_bs_2547_: *mut LeanObject,
    mut v___y_2548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: usize = 0;
    let mut v___x_2558_: usize = 0;
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2550_ = lean_usize_dec_lt(v_i_2546_, v_sz_2545_);
                if v___x_2550_ == 0 {
                    v___x_2551_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2551_, 0, v_bs_2547_);
                    return v___x_2551_;
                } else {
                    v_v_2552_ = lean_array_uget_borrowed(v_bs_2547_, v_i_2546_);
                    v___x_2553_ = l_Lean_IR_ToIR_lowerArg___redArg(v_v_2552_, v___y_2548_);
                    if lean_obj_tag(v___x_2553_) == 0 {
                        v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
                        lean_inc(v_a_2554_);
                        lean_dec_ref_known(v___x_2553_, 1);
                        v___x_2555_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2556_ = lean_array_uset(v_bs_2547_, v_i_2546_, v___x_2555_);
                        v___x_2557_ = 1usize;
                        v___x_2558_ = lean_usize_add(v_i_2546_, v___x_2557_);
                        v___x_2559_ = lean_array_uset(v_bs_x27_2556_, v_i_2546_, v_a_2554_);
                        v_i_2546_ = v___x_2558_;
                        v_bs_2547_ = v___x_2559_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2547_);
                        v_a_2561_ = lean_ctor_get(v___x_2553_, 0);
                        v_isSharedCheck_2568_ = (!lean_is_exclusive(v___x_2553_)) as u8;
                        if v_isSharedCheck_2568_ == 0 {
                            v___x_2563_ = v___x_2553_;
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2561_);
                            lean_dec(v___x_2553_);
                            v___x_2563_ = lean_box(0);
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2564_ == 0 {
                    v___x_2566_ = v___x_2563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(
    mut v_sz_2569_: *mut LeanObject,
    mut v_i_2570_: *mut LeanObject,
    mut v_bs_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2574_: usize = 0;
    let mut v_i_boxed_2575_: usize = 0;
    let mut v_res_2576_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2574_ = lean_unbox_usize(v_sz_2569_);
    lean_dec(v_sz_2569_);
    v_i_boxed_2575_ = lean_unbox_usize(v_i_2570_);
    lean_dec(v_i_2570_);
    v_res_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_boxed_2574_, v_i_boxed_2575_, v_bs_2571_, v___y_2572_);
    lean_dec(v___y_2572_);
    return v_res_2576_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(
    mut v_sz_2577_: usize,
    mut v_i_2578_: usize,
    mut v_bs_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: usize = 0;
    let mut v___x_2590_: usize = 0;
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2582_ = lean_usize_dec_lt(v_i_2578_, v_sz_2577_);
                if v___x_2582_ == 0 {
                    v___x_2583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2583_, 0, v_bs_2579_);
                    return v___x_2583_;
                } else {
                    v_v_2584_ = lean_array_uget_borrowed(v_bs_2579_, v_i_2578_);
                    lean_inc(v_v_2584_);
                    v___x_2585_ = l_Lean_IR_ToIR_lowerParam___redArg(v_v_2584_, v___y_2580_);
                    if lean_obj_tag(v___x_2585_) == 0 {
                        v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
                        lean_inc(v_a_2586_);
                        lean_dec_ref_known(v___x_2585_, 1);
                        v___x_2587_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2588_ = lean_array_uset(v_bs_2579_, v_i_2578_, v___x_2587_);
                        v___x_2589_ = 1usize;
                        v___x_2590_ = lean_usize_add(v_i_2578_, v___x_2589_);
                        v___x_2591_ = lean_array_uset(v_bs_x27_2588_, v_i_2578_, v_a_2586_);
                        v_i_2578_ = v___x_2590_;
                        v_bs_2579_ = v___x_2591_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2579_);
                        v_a_2593_ = lean_ctor_get(v___x_2585_, 0);
                        v_isSharedCheck_2600_ = (!lean_is_exclusive(v___x_2585_)) as u8;
                        if v_isSharedCheck_2600_ == 0 {
                            v___x_2595_ = v___x_2585_;
                            v_isShared_2596_ = v_isSharedCheck_2600_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2593_);
                            lean_dec(v___x_2585_);
                            v___x_2595_ = lean_box(0);
                            v_isShared_2596_ = v_isSharedCheck_2600_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2596_ == 0 {
                    v___x_2598_ = v___x_2595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
                    v___x_2598_ = v_reuseFailAlloc_2599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg___boxed(
    mut v_sz_2601_: *mut LeanObject,
    mut v_i_2602_: *mut LeanObject,
    mut v_bs_2603_: *mut LeanObject,
    mut v___y_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2606_: usize = 0;
    let mut v_i_boxed_2607_: usize = 0;
    let mut v_res_2608_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2606_ = lean_unbox_usize(v_sz_2601_);
    lean_dec(v_sz_2601_);
    v_i_boxed_2607_ = lean_unbox_usize(v_i_2602_);
    lean_dec(v_i_2602_);
    v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_boxed_2606_, v_i_boxed_2607_, v_bs_2603_, v___y_2604_);
    lean_dec(v___y_2604_);
    return v_res_2608_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__2(
    mut v_i_2609_: *mut LeanObject,
    mut v_continueLet_2610_: *mut LeanObject,
    mut v_var_2611_: *mut LeanObject,
    mut v___y_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    v___x_2616_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2616_, 0, v_i_2609_);
    lean_ctor_set(v___x_2616_, 1, v_var_2611_);
    lean_inc(v___y_2614_);
    lean_inc_ref(v___y_2613_);
    lean_inc(v___y_2612_);
    v___x_2617_ = lean_apply_5(
        v_continueLet_2610_,
        v___x_2616_,
        v___y_2612_,
        v___y_2613_,
        v___y_2614_,
        lean_box(0),
    );
    return v___x_2617_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__2___boxed(
    mut v_i_2618_: *mut LeanObject,
    mut v_continueLet_2619_: *mut LeanObject,
    mut v_var_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Lean_IR_ToIR_lowerLet___lam__2(
        v_i_2618_,
        v_continueLet_2619_,
        v_var_2620_,
        v___y_2621_,
        v___y_2622_,
        v___y_2623_,
    );
    lean_dec(v___y_2623_);
    lean_dec_ref(v___y_2622_);
    lean_dec(v___y_2621_);
    return v_res_2625_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__4(
    mut v_n_2626_: *mut LeanObject,
    mut v_offset_2627_: *mut LeanObject,
    mut v_continueLet_2628_: *mut LeanObject,
    mut v_var_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    v___x_2634_ = lean_alloc_ctor(5, 3, (0) as u32);
    lean_ctor_set(v___x_2634_, 0, v_n_2626_);
    lean_ctor_set(v___x_2634_, 1, v_offset_2627_);
    lean_ctor_set(v___x_2634_, 2, v_var_2629_);
    lean_inc(v___y_2632_);
    lean_inc_ref(v___y_2631_);
    lean_inc(v___y_2630_);
    v___x_2635_ = lean_apply_5(
        v_continueLet_2628_,
        v___x_2634_,
        v___y_2630_,
        v___y_2631_,
        v___y_2632_,
        lean_box(0),
    );
    return v___x_2635_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__4___boxed(
    mut v_n_2636_: *mut LeanObject,
    mut v_offset_2637_: *mut LeanObject,
    mut v_continueLet_2638_: *mut LeanObject,
    mut v_var_2639_: *mut LeanObject,
    mut v___y_2640_: *mut LeanObject,
    mut v___y_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2644_: *mut LeanObject = core::ptr::null_mut();
    v_res_2644_ = l_Lean_IR_ToIR_lowerLet___lam__4(
        v_n_2636_,
        v_offset_2637_,
        v_continueLet_2638_,
        v_var_2639_,
        v___y_2640_,
        v___y_2641_,
        v___y_2642_,
    );
    lean_dec(v___y_2642_);
    lean_dec_ref(v___y_2641_);
    lean_dec(v___y_2640_);
    return v_res_2644_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__5(
    mut v_n_2645_: *mut LeanObject,
    mut v_continueLet_2646_: *mut LeanObject,
    mut v_var_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    v___x_2652_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2652_, 0, v_n_2645_);
    lean_ctor_set(v___x_2652_, 1, v_var_2647_);
    lean_inc(v___y_2650_);
    lean_inc_ref(v___y_2649_);
    lean_inc(v___y_2648_);
    v___x_2653_ = lean_apply_5(
        v_continueLet_2646_,
        v___x_2652_,
        v___y_2648_,
        v___y_2649_,
        v___y_2650_,
        lean_box(0),
    );
    return v___x_2653_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__5___boxed(
    mut v_n_2654_: *mut LeanObject,
    mut v_continueLet_2655_: *mut LeanObject,
    mut v_var_2656_: *mut LeanObject,
    mut v___y_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2661_: *mut LeanObject = core::ptr::null_mut();
    v_res_2661_ = l_Lean_IR_ToIR_lowerLet___lam__5(
        v_n_2654_,
        v_continueLet_2655_,
        v_var_2656_,
        v___y_2657_,
        v___y_2658_,
        v___y_2659_,
    );
    lean_dec(v___y_2659_);
    lean_dec_ref(v___y_2658_);
    lean_dec(v___y_2657_);
    return v_res_2661_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__8(
    mut v_continueLet_2662_: *mut LeanObject,
    mut v_var_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    v___x_2668_ = lean_alloc_ctor(10, 1, (0) as u32);
    lean_ctor_set(v___x_2668_, 0, v_var_2663_);
    lean_inc(v___y_2666_);
    lean_inc_ref(v___y_2665_);
    lean_inc(v___y_2664_);
    v___x_2669_ = lean_apply_5(
        v_continueLet_2662_,
        v___x_2668_,
        v___y_2664_,
        v___y_2665_,
        v___y_2666_,
        lean_box(0),
    );
    return v___x_2669_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__8___boxed(
    mut v_continueLet_2670_: *mut LeanObject,
    mut v_var_2671_: *mut LeanObject,
    mut v___y_2672_: *mut LeanObject,
    mut v___y_2673_: *mut LeanObject,
    mut v___y_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2676_: *mut LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Lean_IR_ToIR_lowerLet___lam__8(
        v_continueLet_2670_,
        v_var_2671_,
        v___y_2672_,
        v___y_2673_,
        v___y_2674_,
    );
    lean_dec(v___y_2674_);
    lean_dec_ref(v___y_2673_);
    lean_dec(v___y_2672_);
    return v_res_2676_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__3(
    mut v_i_2677_: *mut LeanObject,
    mut v_continueLet_2678_: *mut LeanObject,
    mut v_var_2679_: *mut LeanObject,
    mut v___y_2680_: *mut LeanObject,
    mut v___y_2681_: *mut LeanObject,
    mut v___y_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    v___x_2684_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_2684_, 0, v_i_2677_);
    lean_ctor_set(v___x_2684_, 1, v_var_2679_);
    lean_inc(v___y_2682_);
    lean_inc_ref(v___y_2681_);
    lean_inc(v___y_2680_);
    v___x_2685_ = lean_apply_5(
        v_continueLet_2678_,
        v___x_2684_,
        v___y_2680_,
        v___y_2681_,
        v___y_2682_,
        lean_box(0),
    );
    return v___x_2685_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__3___boxed(
    mut v_i_2686_: *mut LeanObject,
    mut v_continueLet_2687_: *mut LeanObject,
    mut v_var_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2693_: *mut LeanObject = core::ptr::null_mut();
    v_res_2693_ = l_Lean_IR_ToIR_lowerLet___lam__3(
        v_i_2686_,
        v_continueLet_2687_,
        v_var_2688_,
        v___y_2689_,
        v___y_2690_,
        v___y_2691_,
    );
    lean_dec(v___y_2691_);
    lean_dec_ref(v___y_2690_);
    lean_dec(v___y_2689_);
    return v_res_2693_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__7(
    mut v_ty_2694_: *mut LeanObject,
    mut v_continueLet_2695_: *mut LeanObject,
    mut v_var_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    v___x_2701_ = l_Lean_IR_toIRType(v_ty_2694_);
    v___x_2702_ = lean_alloc_ctor(9, 2, (0) as u32);
    lean_ctor_set(v___x_2702_, 0, v___x_2701_);
    lean_ctor_set(v___x_2702_, 1, v_var_2696_);
    lean_inc(v___y_2699_);
    lean_inc_ref(v___y_2698_);
    lean_inc(v___y_2697_);
    v___x_2703_ = lean_apply_5(
        v_continueLet_2695_,
        v___x_2702_,
        v___y_2697_,
        v___y_2698_,
        v___y_2699_,
        lean_box(0),
    );
    return v___x_2703_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__7___boxed(
    mut v_ty_2704_: *mut LeanObject,
    mut v_continueLet_2705_: *mut LeanObject,
    mut v_var_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2711_: *mut LeanObject = core::ptr::null_mut();
    v_res_2711_ = l_Lean_IR_ToIR_lowerLet___lam__7(
        v_ty_2704_,
        v_continueLet_2705_,
        v_var_2706_,
        v___y_2707_,
        v___y_2708_,
        v___y_2709_,
    );
    lean_dec(v___y_2709_);
    lean_dec_ref(v___y_2708_);
    lean_dec(v___y_2707_);
    lean_dec_ref(v_ty_2704_);
    return v_res_2711_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__6(
    mut v_args_2712_: *mut LeanObject,
    mut v_i_2713_: *mut LeanObject,
    mut v_updateHeader_2714_: u8,
    mut v_continueLet_2715_: *mut LeanObject,
    mut v_var_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2721_: usize = 0;
    let mut v___x_2722_: usize = 0;
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2738_: u8 = 0;
    let mut v_a_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2721_ = lean_array_size(v_args_2712_);
                v___x_2722_ = 0usize;
                v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_2721_, v___x_2722_, v_args_2712_, v___y_2717_);
                if lean_obj_tag(v___x_2723_) == 0 {
                    v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
                    lean_inc(v_a_2724_);
                    lean_dec_ref_known(v___x_2723_, 1);
                    v_name_2725_ = lean_ctor_get(v_i_2713_, 0);
                    v_cidx_2726_ = lean_ctor_get(v_i_2713_, 1);
                    v_size_2727_ = lean_ctor_get(v_i_2713_, 2);
                    v_usize_2728_ = lean_ctor_get(v_i_2713_, 3);
                    v_ssize_2729_ = lean_ctor_get(v_i_2713_, 4);
                    v_isSharedCheck_2738_ = (!lean_is_exclusive(v_i_2713_)) as u8;
                    if v_isSharedCheck_2738_ == 0 {
                        v___x_2731_ = v_i_2713_;
                        v_isShared_2732_ = v_isSharedCheck_2738_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_ssize_2729_);
                        lean_inc(v_usize_2728_);
                        lean_inc(v_size_2727_);
                        lean_inc(v_cidx_2726_);
                        lean_inc(v_name_2725_);
                        lean_dec(v_i_2713_);
                        v___x_2731_ = lean_box(0);
                        v_isShared_2732_ = v_isSharedCheck_2738_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_var_2716_);
                    lean_dec_ref(v_continueLet_2715_);
                    lean_dec_ref(v_i_2713_);
                    v_a_2739_ = lean_ctor_get(v___x_2723_, 0);
                    v_isSharedCheck_2746_ = (!lean_is_exclusive(v___x_2723_)) as u8;
                    if v_isSharedCheck_2746_ == 0 {
                        v___x_2741_ = v___x_2723_;
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2739_);
                        lean_dec(v___x_2723_);
                        v___x_2741_ = lean_box(0);
                        v_isShared_2742_ = v_isSharedCheck_2746_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2732_ == 0 {
                    v___x_2734_ = v___x_2731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_name_2725_);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_cidx_2726_);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 2, v_size_2727_);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 3, v_usize_2728_);
                    lean_ctor_set(v_reuseFailAlloc_2737_, 4, v_ssize_2729_);
                    v___x_2734_ = v_reuseFailAlloc_2737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2735_ = lean_alloc_ctor(2, 3, (1) as u32);
                lean_ctor_set(v___x_2735_, 0, v_var_2716_);
                lean_ctor_set(v___x_2735_, 1, v___x_2734_);
                lean_ctor_set(v___x_2735_, 2, v_a_2724_);
                lean_ctor_set_uint8(
                    v___x_2735_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_updateHeader_2714_,
                );
                lean_inc(v___y_2719_);
                lean_inc_ref(v___y_2718_);
                lean_inc(v___y_2717_);
                v___x_2736_ = lean_apply_5(
                    v_continueLet_2715_,
                    v___x_2735_,
                    v___y_2717_,
                    v___y_2718_,
                    v___y_2719_,
                    lean_box(0),
                );
                return v___x_2736_;
            }
            3 => {
                if v_isShared_2742_ == 0 {
                    v___x_2744_ = v___x_2741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__6___boxed(
    mut v_args_2747_: *mut LeanObject,
    mut v_i_2748_: *mut LeanObject,
    mut v_updateHeader_2749_: *mut LeanObject,
    mut v_continueLet_2750_: *mut LeanObject,
    mut v_var_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_updateHeader_9660__boxed_2756_: u8 = 0;
    let mut v_res_2757_: *mut LeanObject = core::ptr::null_mut();
    v_updateHeader_9660__boxed_2756_ = (lean_unbox(v_updateHeader_2749_) as u8);
    v_res_2757_ = l_Lean_IR_ToIR_lowerLet___lam__6(
        v_args_2747_,
        v_i_2748_,
        v_updateHeader_9660__boxed_2756_,
        v_continueLet_2750_,
        v_var_2751_,
        v___y_2752_,
        v___y_2753_,
        v___y_2754_,
    );
    lean_dec(v___y_2754_);
    lean_dec_ref(v___y_2753_);
    lean_dec(v___y_2752_);
    return v_res_2757_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__9(
    mut v_continueLet_2758_: *mut LeanObject,
    mut v_var_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    v___x_2764_ = lean_alloc_ctor(12, 1, (0) as u32);
    lean_ctor_set(v___x_2764_, 0, v_var_2759_);
    lean_inc(v___y_2762_);
    lean_inc_ref(v___y_2761_);
    lean_inc(v___y_2760_);
    v___x_2765_ = lean_apply_5(
        v_continueLet_2758_,
        v___x_2764_,
        v___y_2760_,
        v___y_2761_,
        v___y_2762_,
        lean_box(0),
    );
    return v___x_2765_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__9___boxed(
    mut v_continueLet_2766_: *mut LeanObject,
    mut v_var_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2772_: *mut LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_IR_ToIR_lowerLet___lam__9(
        v_continueLet_2766_,
        v_var_2767_,
        v___y_2768_,
        v___y_2769_,
        v___y_2770_,
    );
    lean_dec(v___y_2770_);
    lean_dec_ref(v___y_2769_);
    lean_dec(v___y_2768_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__1(
    mut v_args_2773_: *mut LeanObject,
    mut v_continueLet_2774_: *mut LeanObject,
    mut v_id_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2780_: usize = 0;
    let mut v___x_2781_: usize = 0;
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2789_: u8 = 0;
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2780_ = lean_array_size(v_args_2773_);
                v___x_2781_ = 0usize;
                v___x_2782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_2780_, v___x_2781_, v_args_2773_, v___y_2776_);
                if lean_obj_tag(v___x_2782_) == 0 {
                    v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
                    lean_inc(v_a_2783_);
                    lean_dec_ref_known(v___x_2782_, 1);
                    v___x_2784_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v___x_2784_, 0, v_id_2775_);
                    lean_ctor_set(v___x_2784_, 1, v_a_2783_);
                    lean_inc(v___y_2778_);
                    lean_inc_ref(v___y_2777_);
                    lean_inc(v___y_2776_);
                    v___x_2785_ = lean_apply_5(
                        v_continueLet_2774_,
                        v___x_2784_,
                        v___y_2776_,
                        v___y_2777_,
                        v___y_2778_,
                        lean_box(0),
                    );
                    return v___x_2785_;
                } else {
                    lean_dec(v_id_2775_);
                    lean_dec_ref(v_continueLet_2774_);
                    v_a_2786_ = lean_ctor_get(v___x_2782_, 0);
                    v_isSharedCheck_2793_ = (!lean_is_exclusive(v___x_2782_)) as u8;
                    if v_isSharedCheck_2793_ == 0 {
                        v___x_2788_ = v___x_2782_;
                        v_isShared_2789_ = v_isSharedCheck_2793_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2786_);
                        lean_dec(v___x_2782_);
                        v___x_2788_ = lean_box(0);
                        v_isShared_2789_ = v_isSharedCheck_2793_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2789_ == 0 {
                    v___x_2791_ = v___x_2788_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
                    v___x_2791_ = v_reuseFailAlloc_2792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2791_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__1___boxed(
    mut v_args_2794_: *mut LeanObject,
    mut v_continueLet_2795_: *mut LeanObject,
    mut v_id_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
    mut v___y_2798_: *mut LeanObject,
    mut v___y_2799_: *mut LeanObject,
    mut v___y_2800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2801_: *mut LeanObject = core::ptr::null_mut();
    v_res_2801_ = l_Lean_IR_ToIR_lowerLet___lam__1(
        v_args_2794_,
        v_continueLet_2795_,
        v_id_2796_,
        v___y_2797_,
        v___y_2798_,
        v___y_2799_,
    );
    lean_dec(v___y_2799_);
    lean_dec_ref(v___y_2798_);
    lean_dec(v___y_2797_);
    return v_res_2801_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__0(
    mut v_fvarId_2802_: *mut LeanObject,
    mut v_k_2803_: *mut LeanObject,
    mut v_type_2804_: *mut LeanObject,
    mut v_e_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
    mut v___y_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2821_: u8 = 0;
    let mut v_a_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2810_ = l_Lean_IR_ToIR_bindVar___redArg(v_fvarId_2802_, v___y_2806_);
                if lean_obj_tag(v___x_2810_) == 0 {
                    v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
                    lean_inc(v_a_2811_);
                    lean_dec_ref_known(v___x_2810_, 1);
                    v___x_2812_ =
                        l_Lean_IR_ToIR_lowerCode(v_k_2803_, v___y_2806_, v___y_2807_, v___y_2808_);
                    if lean_obj_tag(v___x_2812_) == 0 {
                        v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
                        v_isSharedCheck_2821_ = (!lean_is_exclusive(v___x_2812_)) as u8;
                        if v_isSharedCheck_2821_ == 0 {
                            v___x_2815_ = v___x_2812_;
                            v_isShared_2816_ = v_isSharedCheck_2821_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2813_);
                            lean_dec(v___x_2812_);
                            v___x_2815_ = lean_box(0);
                            v_isShared_2816_ = v_isSharedCheck_2821_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2811_);
                        lean_dec_ref(v_e_2805_);
                        lean_dec(v_type_2804_);
                        return v___x_2812_;
                    }
                } else {
                    lean_dec_ref(v_e_2805_);
                    lean_dec(v_type_2804_);
                    lean_dec_ref(v_k_2803_);
                    v_a_2822_ = lean_ctor_get(v___x_2810_, 0);
                    v_isSharedCheck_2829_ = (!lean_is_exclusive(v___x_2810_)) as u8;
                    if v_isSharedCheck_2829_ == 0 {
                        v___x_2824_ = v___x_2810_;
                        v_isShared_2825_ = v_isSharedCheck_2829_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2822_);
                        lean_dec(v___x_2810_);
                        v___x_2824_ = lean_box(0);
                        v_isShared_2825_ = v_isSharedCheck_2829_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2817_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2817_, 0, v_a_2811_);
                lean_ctor_set(v___x_2817_, 1, v_type_2804_);
                lean_ctor_set(v___x_2817_, 2, v_e_2805_);
                lean_ctor_set(v___x_2817_, 3, v_a_2813_);
                if v_isShared_2816_ == 0 {
                    lean_ctor_set(v___x_2815_, 0, v___x_2817_);
                    v___x_2819_ = v___x_2815_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
                    v___x_2819_ = v_reuseFailAlloc_2820_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2819_;
            }
            3 => {
                if v_isShared_2825_ == 0 {
                    v___x_2827_ = v___x_2824_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
                    v___x_2827_ = v_reuseFailAlloc_2828_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___lam__0___boxed(
    mut v_fvarId_2830_: *mut LeanObject,
    mut v_k_2831_: *mut LeanObject,
    mut v_type_2832_: *mut LeanObject,
    mut v_e_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
    mut v___y_2837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2838_: *mut LeanObject = core::ptr::null_mut();
    v_res_2838_ = l_Lean_IR_ToIR_lowerLet___lam__0(
        v_fvarId_2830_,
        v_k_2831_,
        v_type_2832_,
        v_e_2833_,
        v___y_2834_,
        v___y_2835_,
        v___y_2836_,
    );
    lean_dec(v___y_2836_);
    lean_dec_ref(v___y_2835_);
    lean_dec(v___y_2834_);
    return v_res_2838_;
}
pub unsafe fn l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(
    mut v_decl_2839_: *mut LeanObject,
    mut v_k_2840_: *mut LeanObject,
    mut v_fvarId_2841_: *mut LeanObject,
    mut v_f_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_a_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2855_: u8 = 0;
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2847_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_2841_, v_a_2843_);
                if lean_obj_tag(v___x_2847_) == 0 {
                    v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
                    lean_inc(v_a_2848_);
                    lean_dec_ref_known(v___x_2847_, 1);
                    if lean_obj_tag(v_a_2848_) == 0 {
                        lean_dec_ref(v_k_2840_);
                        lean_dec_ref(v_decl_2839_);
                        v_id_2849_ = lean_ctor_get(v_a_2848_, 0);
                        lean_inc(v_id_2849_);
                        lean_dec_ref_known(v_a_2848_, 1);
                        lean_inc(v_a_2845_);
                        lean_inc_ref(v_a_2844_);
                        lean_inc(v_a_2843_);
                        v___x_2850_ = lean_apply_5(
                            v_f_2842_,
                            v_id_2849_,
                            v_a_2843_,
                            v_a_2844_,
                            v_a_2845_,
                            lean_box(0),
                        );
                        return v___x_2850_;
                    } else {
                        lean_dec_ref(v_f_2842_);
                        v___x_2851_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_2839_, v_k_2840_, v_a_2843_, v_a_2844_, v_a_2845_);
                        return v___x_2851_;
                    }
                } else {
                    lean_dec_ref(v_f_2842_);
                    lean_dec_ref(v_k_2840_);
                    lean_dec_ref(v_decl_2839_);
                    v_a_2852_ = lean_ctor_get(v___x_2847_, 0);
                    v_isSharedCheck_2859_ = (!lean_is_exclusive(v___x_2847_)) as u8;
                    if v_isSharedCheck_2859_ == 0 {
                        v___x_2854_ = v___x_2847_;
                        v_isShared_2855_ = v_isSharedCheck_2859_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2852_);
                        lean_dec(v___x_2847_);
                        v___x_2854_ = lean_box(0);
                        v_isShared_2855_ = v_isSharedCheck_2859_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2855_ == 0 {
                    v___x_2857_ = v___x_2854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
                    v___x_2857_ = v_reuseFailAlloc_2858_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet(
    mut v_decl_2860_: *mut LeanObject,
    mut v_k_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_continueLet_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2881_: u8 = 0;
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v_sz_2892_: usize = 0;
    let mut v___x_2893_: usize = 0;
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2903_: u8 = 0;
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut v_a_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2915_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut v_i_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v_sz_2939_: usize = 0;
    let mut v___x_2940_: usize = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2954_: u8 = 0;
    let mut v_isSharedCheck_2955_: u8 = 0;
    let mut v_fn_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v_sz_2961_: usize = 0;
    let mut v___x_2962_: usize = 0;
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_isSharedCheck_2977_: u8 = 0;
    let mut v_n_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_var_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updateHeader_2984_: u8 = 0;
    let mut v_args_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_2866_ = lean_ctor_get(v_decl_2860_, 0);
                v_type_2867_ = lean_ctor_get(v_decl_2860_, 2);
                v_value_2868_ = lean_ctor_get(v_decl_2860_, 3);
                lean_inc(v_value_2868_);
                v_type_2869_ = l_Lean_IR_toIRType(v_type_2867_);
                lean_inc(v_type_2869_);
                lean_inc_ref(v_k_2861_);
                lean_inc(v_fvarId_2866_);
                v_continueLet_2870_ = lean_alloc_closure(
                    l_Lean_IR_ToIR_lowerLet___lam__0___boxed as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v_continueLet_2870_, 0, v_fvarId_2866_);
                lean_closure_set(v_continueLet_2870_, 1, v_k_2861_);
                lean_closure_set(v_continueLet_2870_, 2, v_type_2869_);
                match lean_obj_tag(v_value_2868_) {
                    0 => {
                        lean_inc(v_fvarId_2866_);
                        lean_dec_ref(v_continueLet_2870_);
                        lean_dec_ref(v_decl_2860_);
                        v_value_2871_ = lean_ctor_get(v_value_2868_, 0);
                        v_isSharedCheck_2881_ = (!lean_is_exclusive(v_value_2868_)) as u8;
                        if v_isSharedCheck_2881_ == 0 {
                            v___x_2873_ = v_value_2868_;
                            v_isShared_2874_ = v_isSharedCheck_2881_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_value_2871_);
                            lean_dec(v_value_2868_);
                            v___x_2873_ = lean_box(0);
                            v_isShared_2874_ = v_isSharedCheck_2881_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        lean_dec_ref(v_continueLet_2870_);
                        lean_dec(v_type_2869_);
                        v___x_2882_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(v_decl_2860_, v_k_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
                        return v___x_2882_;
                    }
                    4 => {
                        lean_dec(v_type_2869_);
                        v_fvarId_2883_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_fvarId_2883_);
                        v_args_2884_ = lean_ctor_get(v_value_2868_, 1);
                        lean_inc_ref(v_args_2884_);
                        lean_dec_ref_known(v_value_2868_, 2);
                        v___f_2885_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__1___boxed as *mut core::ffi::c_void,
                            7,
                            2,
                        );
                        lean_closure_set(v___f_2885_, 0, v_args_2884_);
                        lean_closure_set(v___f_2885_, 1, v_continueLet_2870_);
                        v___x_2886_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_fvarId_2883_, v___f_2885_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_fvarId_2883_);
                        return v___x_2886_;
                    }
                    5 => {
                        lean_inc(v_fvarId_2866_);
                        lean_dec_ref(v_continueLet_2870_);
                        lean_dec_ref(v_decl_2860_);
                        v_i_2887_ = lean_ctor_get(v_value_2868_, 0);
                        v_args_2888_ = lean_ctor_get(v_value_2868_, 1);
                        v_isSharedCheck_2920_ = (!lean_is_exclusive(v_value_2868_)) as u8;
                        if v_isSharedCheck_2920_ == 0 {
                            v___x_2890_ = v_value_2868_;
                            v_isShared_2891_ = v_isSharedCheck_2920_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_args_2888_);
                            lean_inc(v_i_2887_);
                            lean_dec(v_value_2868_);
                            v___x_2890_ = lean_box(0);
                            v_isShared_2891_ = v_isSharedCheck_2920_;
                            state = 3;
                            continue;
                        }
                    }
                    6 => {
                        lean_dec(v_type_2869_);
                        v_i_2921_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_i_2921_);
                        v_var_2922_ = lean_ctor_get(v_value_2868_, 1);
                        lean_inc(v_var_2922_);
                        lean_dec_ref_known(v_value_2868_, 2);
                        v___f_2923_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__2___boxed as *mut core::ffi::c_void,
                            7,
                            2,
                        );
                        lean_closure_set(v___f_2923_, 0, v_i_2921_);
                        lean_closure_set(v___f_2923_, 1, v_continueLet_2870_);
                        v___x_2924_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_var_2922_, v___f_2923_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_var_2922_);
                        return v___x_2924_;
                    }
                    7 => {
                        lean_dec(v_type_2869_);
                        v_i_2925_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_i_2925_);
                        v_var_2926_ = lean_ctor_get(v_value_2868_, 1);
                        lean_inc(v_var_2926_);
                        lean_dec_ref_known(v_value_2868_, 2);
                        v___f_2927_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__3___boxed as *mut core::ffi::c_void,
                            7,
                            2,
                        );
                        lean_closure_set(v___f_2927_, 0, v_i_2925_);
                        lean_closure_set(v___f_2927_, 1, v_continueLet_2870_);
                        v___x_2928_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_var_2926_, v___f_2927_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_var_2926_);
                        return v___x_2928_;
                    }
                    8 => {
                        lean_dec(v_type_2869_);
                        v_n_2929_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_n_2929_);
                        v_offset_2930_ = lean_ctor_get(v_value_2868_, 1);
                        lean_inc(v_offset_2930_);
                        v_var_2931_ = lean_ctor_get(v_value_2868_, 2);
                        lean_inc(v_var_2931_);
                        lean_dec_ref_known(v_value_2868_, 3);
                        v___f_2932_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__4___boxed as *mut core::ffi::c_void,
                            8,
                            3,
                        );
                        lean_closure_set(v___f_2932_, 0, v_n_2929_);
                        lean_closure_set(v___f_2932_, 1, v_offset_2930_);
                        lean_closure_set(v___f_2932_, 2, v_continueLet_2870_);
                        v___x_2933_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_var_2931_, v___f_2932_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_var_2931_);
                        return v___x_2933_;
                    }
                    9 => {
                        lean_inc(v_fvarId_2866_);
                        lean_dec_ref(v_continueLet_2870_);
                        lean_dec_ref(v_decl_2860_);
                        v_fn_2934_ = lean_ctor_get(v_value_2868_, 0);
                        v_args_2935_ = lean_ctor_get(v_value_2868_, 1);
                        v_isSharedCheck_2955_ = (!lean_is_exclusive(v_value_2868_)) as u8;
                        if v_isSharedCheck_2955_ == 0 {
                            v___x_2937_ = v_value_2868_;
                            v_isShared_2938_ = v_isSharedCheck_2955_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_args_2935_);
                            lean_inc(v_fn_2934_);
                            lean_dec(v_value_2868_);
                            v___x_2937_ = lean_box(0);
                            v_isShared_2938_ = v_isSharedCheck_2955_;
                            state = 9;
                            continue;
                        }
                    }
                    10 => {
                        lean_inc(v_fvarId_2866_);
                        lean_dec_ref(v_continueLet_2870_);
                        lean_dec_ref(v_decl_2860_);
                        v_fn_2956_ = lean_ctor_get(v_value_2868_, 0);
                        v_args_2957_ = lean_ctor_get(v_value_2868_, 1);
                        v_isSharedCheck_2977_ = (!lean_is_exclusive(v_value_2868_)) as u8;
                        if v_isSharedCheck_2977_ == 0 {
                            v___x_2959_ = v_value_2868_;
                            v_isShared_2960_ = v_isSharedCheck_2977_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_args_2957_);
                            lean_inc(v_fn_2956_);
                            lean_dec(v_value_2868_);
                            v___x_2959_ = lean_box(0);
                            v_isShared_2960_ = v_isSharedCheck_2977_;
                            state = 13;
                            continue;
                        }
                    }
                    11 => {
                        lean_dec(v_type_2869_);
                        v_n_2978_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_n_2978_);
                        v_var_2979_ = lean_ctor_get(v_value_2868_, 1);
                        lean_inc(v_var_2979_);
                        lean_dec_ref_known(v_value_2868_, 2);
                        v___f_2980_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__5___boxed as *mut core::ffi::c_void,
                            7,
                            2,
                        );
                        lean_closure_set(v___f_2980_, 0, v_n_2978_);
                        lean_closure_set(v___f_2980_, 1, v_continueLet_2870_);
                        v___x_2981_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_var_2979_, v___f_2980_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_var_2979_);
                        return v___x_2981_;
                    }
                    12 => {
                        lean_dec(v_type_2869_);
                        v_var_2982_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_var_2982_);
                        v_i_2983_ = lean_ctor_get(v_value_2868_, 1);
                        lean_inc_ref(v_i_2983_);
                        v_updateHeader_2984_ = lean_ctor_get_uint8(
                            v_value_2868_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_args_2985_ = lean_ctor_get(v_value_2868_, 2);
                        lean_inc_ref(v_args_2985_);
                        lean_dec_ref_known(v_value_2868_, 3);
                        v___x_2986_ = lean_box((v_updateHeader_2984_) as usize);
                        v___f_2987_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__6___boxed as *mut core::ffi::c_void,
                            9,
                            4,
                        );
                        lean_closure_set(v___f_2987_, 0, v_args_2985_);
                        lean_closure_set(v___f_2987_, 1, v_i_2983_);
                        lean_closure_set(v___f_2987_, 2, v___x_2986_);
                        lean_closure_set(v___f_2987_, 3, v_continueLet_2870_);
                        v___x_2988_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_var_2982_, v___f_2987_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_var_2982_);
                        return v___x_2988_;
                    }
                    13 => {
                        lean_dec(v_type_2869_);
                        v_ty_2989_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc_ref(v_ty_2989_);
                        v_fvarId_2990_ = lean_ctor_get(v_value_2868_, 1);
                        lean_inc(v_fvarId_2990_);
                        lean_dec_ref_known(v_value_2868_, 2);
                        v___f_2991_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__7___boxed as *mut core::ffi::c_void,
                            7,
                            2,
                        );
                        lean_closure_set(v___f_2991_, 0, v_ty_2989_);
                        lean_closure_set(v___f_2991_, 1, v_continueLet_2870_);
                        v___x_2992_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_fvarId_2990_, v___f_2991_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_fvarId_2990_);
                        return v___x_2992_;
                    }
                    14 => {
                        lean_dec(v_type_2869_);
                        v_fvarId_2993_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_fvarId_2993_);
                        lean_dec_ref_known(v_value_2868_, 1);
                        v___f_2994_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__8___boxed as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        lean_closure_set(v___f_2994_, 0, v_continueLet_2870_);
                        v___x_2995_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_fvarId_2993_, v___f_2994_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_fvarId_2993_);
                        return v___x_2995_;
                    }
                    _ => {
                        lean_dec(v_type_2869_);
                        v_fvarId_2996_ = lean_ctor_get(v_value_2868_, 0);
                        lean_inc(v_fvarId_2996_);
                        lean_dec_ref_known(v_value_2868_, 1);
                        v___f_2997_ = lean_alloc_closure(
                            l_Lean_IR_ToIR_lowerLet___lam__9___boxed as *mut core::ffi::c_void,
                            6,
                            1,
                        );
                        lean_closure_set(v___f_2997_, 0, v_continueLet_2870_);
                        v___x_2998_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(v_decl_2860_, v_k_2861_, v_fvarId_2996_, v___f_2997_, v_a_2862_, v_a_2863_, v_a_2864_);
                        lean_dec(v_fvarId_2996_);
                        return v___x_2998_;
                    }
                }
            }
            1 => {
                v___x_2875_ = l_Lean_IR_ToIR_lowerLitValue(v_value_2871_);
                v_fst_2876_ = lean_ctor_get(v___x_2875_, 0);
                lean_inc(v_fst_2876_);
                lean_dec_ref(v___x_2875_);
                if v_isShared_2874_ == 0 {
                    lean_ctor_set_tag(v___x_2873_, 11);
                    lean_ctor_set(v___x_2873_, 0, v_fst_2876_);
                    v___x_2878_ = v___x_2873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2880_ = lean_alloc_ctor(11, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_fst_2876_);
                    v___x_2878_ = v_reuseFailAlloc_2880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2879_ = l_Lean_IR_ToIR_lowerLet___lam__0(
                    v_fvarId_2866_,
                    v_k_2861_,
                    v_type_2869_,
                    v___x_2878_,
                    v_a_2862_,
                    v_a_2863_,
                    v_a_2864_,
                );
                return v___x_2879_;
            }
            3 => {
                v_sz_2892_ = lean_array_size(v_args_2888_);
                v___x_2893_ = 0usize;
                v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_2892_, v___x_2893_, v_args_2888_, v_a_2862_);
                if lean_obj_tag(v___x_2894_) == 0 {
                    v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
                    lean_inc(v_a_2895_);
                    lean_dec_ref_known(v___x_2894_, 1);
                    v_name_2896_ = lean_ctor_get(v_i_2887_, 0);
                    v_cidx_2897_ = lean_ctor_get(v_i_2887_, 1);
                    v_size_2898_ = lean_ctor_get(v_i_2887_, 2);
                    v_usize_2899_ = lean_ctor_get(v_i_2887_, 3);
                    v_ssize_2900_ = lean_ctor_get(v_i_2887_, 4);
                    v_isSharedCheck_2911_ = (!lean_is_exclusive(v_i_2887_)) as u8;
                    if v_isSharedCheck_2911_ == 0 {
                        v___x_2902_ = v_i_2887_;
                        v_isShared_2903_ = v_isSharedCheck_2911_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_ssize_2900_);
                        lean_inc(v_usize_2899_);
                        lean_inc(v_size_2898_);
                        lean_inc(v_cidx_2897_);
                        lean_inc(v_name_2896_);
                        lean_dec(v_i_2887_);
                        v___x_2902_ = lean_box(0);
                        v_isShared_2903_ = v_isSharedCheck_2911_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2890_);
                    lean_dec_ref(v_i_2887_);
                    lean_dec(v_type_2869_);
                    lean_dec(v_fvarId_2866_);
                    lean_dec_ref(v_k_2861_);
                    v_a_2912_ = lean_ctor_get(v___x_2894_, 0);
                    v_isSharedCheck_2919_ = (!lean_is_exclusive(v___x_2894_)) as u8;
                    if v_isSharedCheck_2919_ == 0 {
                        v___x_2914_ = v___x_2894_;
                        v_isShared_2915_ = v_isSharedCheck_2919_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2912_);
                        lean_dec(v___x_2894_);
                        v___x_2914_ = lean_box(0);
                        v_isShared_2915_ = v_isSharedCheck_2919_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2903_ == 0 {
                    v___x_2905_ = v___x_2902_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_name_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_cidx_2897_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 2, v_size_2898_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 3, v_usize_2899_);
                    lean_ctor_set(v_reuseFailAlloc_2910_, 4, v_ssize_2900_);
                    v___x_2905_ = v_reuseFailAlloc_2910_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2891_ == 0 {
                    lean_ctor_set_tag(v___x_2890_, 0);
                    lean_ctor_set(v___x_2890_, 1, v_a_2895_);
                    lean_ctor_set(v___x_2890_, 0, v___x_2905_);
                    v___x_2907_ = v___x_2890_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2905_);
                    lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_a_2895_);
                    v___x_2907_ = v_reuseFailAlloc_2909_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2908_ = l_Lean_IR_ToIR_lowerLet___lam__0(
                    v_fvarId_2866_,
                    v_k_2861_,
                    v_type_2869_,
                    v___x_2907_,
                    v_a_2862_,
                    v_a_2863_,
                    v_a_2864_,
                );
                return v___x_2908_;
            }
            7 => {
                if v_isShared_2915_ == 0 {
                    v___x_2917_ = v___x_2914_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
                    v___x_2917_ = v_reuseFailAlloc_2918_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2917_;
            }
            9 => {
                v_sz_2939_ = lean_array_size(v_args_2935_);
                v___x_2940_ = 0usize;
                v___x_2941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_2939_, v___x_2940_, v_args_2935_, v_a_2862_);
                if lean_obj_tag(v___x_2941_) == 0 {
                    v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
                    lean_inc(v_a_2942_);
                    lean_dec_ref_known(v___x_2941_, 1);
                    if v_isShared_2938_ == 0 {
                        lean_ctor_set_tag(v___x_2937_, 6);
                        lean_ctor_set(v___x_2937_, 1, v_a_2942_);
                        v___x_2944_ = v___x_2937_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2946_ = lean_alloc_ctor(6, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_fn_2934_);
                        lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_a_2942_);
                        v___x_2944_ = v_reuseFailAlloc_2946_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2937_);
                    lean_dec(v_fn_2934_);
                    lean_dec(v_type_2869_);
                    lean_dec(v_fvarId_2866_);
                    lean_dec_ref(v_k_2861_);
                    v_a_2947_ = lean_ctor_get(v___x_2941_, 0);
                    v_isSharedCheck_2954_ = (!lean_is_exclusive(v___x_2941_)) as u8;
                    if v_isSharedCheck_2954_ == 0 {
                        v___x_2949_ = v___x_2941_;
                        v_isShared_2950_ = v_isSharedCheck_2954_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2947_);
                        lean_dec(v___x_2941_);
                        v___x_2949_ = lean_box(0);
                        v_isShared_2950_ = v_isSharedCheck_2954_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                v___x_2945_ = l_Lean_IR_ToIR_lowerLet___lam__0(
                    v_fvarId_2866_,
                    v_k_2861_,
                    v_type_2869_,
                    v___x_2944_,
                    v_a_2862_,
                    v_a_2863_,
                    v_a_2864_,
                );
                return v___x_2945_;
            }
            11 => {
                if v_isShared_2950_ == 0 {
                    v___x_2952_ = v___x_2949_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
                    v___x_2952_ = v_reuseFailAlloc_2953_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2952_;
            }
            13 => {
                v_sz_2961_ = lean_array_size(v_args_2957_);
                v___x_2962_ = 0usize;
                v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_2961_, v___x_2962_, v_args_2957_, v_a_2862_);
                if lean_obj_tag(v___x_2963_) == 0 {
                    v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
                    lean_inc(v_a_2964_);
                    lean_dec_ref_known(v___x_2963_, 1);
                    if v_isShared_2960_ == 0 {
                        lean_ctor_set_tag(v___x_2959_, 7);
                        lean_ctor_set(v___x_2959_, 1, v_a_2964_);
                        v___x_2966_ = v___x_2959_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2968_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_fn_2956_);
                        lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_a_2964_);
                        v___x_2966_ = v_reuseFailAlloc_2968_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2959_);
                    lean_dec(v_fn_2956_);
                    lean_dec(v_type_2869_);
                    lean_dec(v_fvarId_2866_);
                    lean_dec_ref(v_k_2861_);
                    v_a_2969_ = lean_ctor_get(v___x_2963_, 0);
                    v_isSharedCheck_2976_ = (!lean_is_exclusive(v___x_2963_)) as u8;
                    if v_isSharedCheck_2976_ == 0 {
                        v___x_2971_ = v___x_2963_;
                        v_isShared_2972_ = v_isSharedCheck_2976_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2969_);
                        lean_dec(v___x_2963_);
                        v___x_2971_ = lean_box(0);
                        v_isShared_2972_ = v_isSharedCheck_2976_;
                        state = 15;
                        continue;
                    }
                }
            }
            14 => {
                v___x_2967_ = l_Lean_IR_ToIR_lowerLet___lam__0(
                    v_fvarId_2866_,
                    v_k_2861_,
                    v_type_2869_,
                    v___x_2966_,
                    v_a_2862_,
                    v_a_2863_,
                    v_a_2864_,
                );
                return v___x_2967_;
            }
            15 => {
                if v_isShared_2972_ == 0 {
                    v___x_2974_ = v___x_2971_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
                    v___x_2974_ = v_reuseFailAlloc_2975_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__3() -> *mut LeanObject {
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    v___x_3002_ = l_Lean_IR_ToIR_lowerCode___closed__2;
    v___x_3003_ = lean_unsigned_to_nat(15);
    v___x_3004_ = lean_unsigned_to_nat(128);
    v___x_3005_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3006_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3007_ = l_mkPanicMessageWithDecl(
        v___x_3006_,
        v___x_3005_,
        v___x_3004_,
        v___x_3003_,
        v___x_3002_,
    );
    return v___x_3007_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerAlt(
    mut v_a_3008_: *mut LeanObject,
    mut v_a_3009_: *mut LeanObject,
    mut v_a_3010_: *mut LeanObject,
    mut v_a_3011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3022_: u8 = 0;
    let mut v_name_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut v_a_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_code_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3066_: u8 = 0;
    let mut v_a_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3070_: u8 = 0;
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3074_: u8 = 0;
    let mut v_isSharedCheck_3075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3008_) == 1 {
                    v_info_3013_ = lean_ctor_get(v_a_3008_, 0);
                    v_code_3014_ = lean_ctor_get(v_a_3008_, 1);
                    v_isSharedCheck_3050_ = (!lean_is_exclusive(v_a_3008_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3016_ = v_a_3008_;
                        v_isShared_3017_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_3014_);
                        lean_inc(v_info_3013_);
                        lean_dec(v_a_3008_);
                        v___x_3016_ = lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_code_3051_ = lean_ctor_get(v_a_3008_, 0);
                    v_isSharedCheck_3075_ = (!lean_is_exclusive(v_a_3008_)) as u8;
                    if v_isSharedCheck_3075_ == 0 {
                        v___x_3053_ = v_a_3008_;
                        v_isShared_3054_ = v_isSharedCheck_3075_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_code_3051_);
                        lean_dec(v_a_3008_);
                        v___x_3053_ = lean_box(0);
                        v_isShared_3054_ = v_isSharedCheck_3075_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3018_ =
                    l_Lean_IR_ToIR_lowerCode(v_code_3014_, v_a_3009_, v_a_3010_, v_a_3011_);
                if lean_obj_tag(v___x_3018_) == 0 {
                    v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
                    v_isSharedCheck_3041_ = (!lean_is_exclusive(v___x_3018_)) as u8;
                    if v_isSharedCheck_3041_ == 0 {
                        v___x_3021_ = v___x_3018_;
                        v_isShared_3022_ = v_isSharedCheck_3041_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3019_);
                        lean_dec(v___x_3018_);
                        v___x_3021_ = lean_box(0);
                        v_isShared_3022_ = v_isSharedCheck_3041_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3016_);
                    lean_dec_ref(v_info_3013_);
                    v_a_3042_ = lean_ctor_get(v___x_3018_, 0);
                    v_isSharedCheck_3049_ = (!lean_is_exclusive(v___x_3018_)) as u8;
                    if v_isSharedCheck_3049_ == 0 {
                        v___x_3044_ = v___x_3018_;
                        v_isShared_3045_ = v_isSharedCheck_3049_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3042_);
                        lean_dec(v___x_3018_);
                        v___x_3044_ = lean_box(0);
                        v_isShared_3045_ = v_isSharedCheck_3049_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_name_3023_ = lean_ctor_get(v_info_3013_, 0);
                v_cidx_3024_ = lean_ctor_get(v_info_3013_, 1);
                v_size_3025_ = lean_ctor_get(v_info_3013_, 2);
                v_usize_3026_ = lean_ctor_get(v_info_3013_, 3);
                v_ssize_3027_ = lean_ctor_get(v_info_3013_, 4);
                v_isSharedCheck_3040_ = (!lean_is_exclusive(v_info_3013_)) as u8;
                if v_isSharedCheck_3040_ == 0 {
                    v___x_3029_ = v_info_3013_;
                    v_isShared_3030_ = v_isSharedCheck_3040_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_ssize_3027_);
                    lean_inc(v_usize_3026_);
                    lean_inc(v_size_3025_);
                    lean_inc(v_cidx_3024_);
                    lean_inc(v_name_3023_);
                    lean_dec(v_info_3013_);
                    v___x_3029_ = lean_box(0);
                    v_isShared_3030_ = v_isSharedCheck_3040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3030_ == 0 {
                    v___x_3032_ = v___x_3029_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_name_3023_);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_cidx_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_size_3025_);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_usize_3026_);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 4, v_ssize_3027_);
                    v___x_3032_ = v_reuseFailAlloc_3039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3017_ == 0 {
                    lean_ctor_set_tag(v___x_3016_, 0);
                    lean_ctor_set(v___x_3016_, 1, v_a_3019_);
                    lean_ctor_set(v___x_3016_, 0, v___x_3032_);
                    v___x_3034_ = v___x_3016_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3032_);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_a_3019_);
                    v___x_3034_ = v_reuseFailAlloc_3038_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3022_ == 0 {
                    lean_ctor_set(v___x_3021_, 0, v___x_3034_);
                    v___x_3036_ = v___x_3021_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3034_);
                    v___x_3036_ = v_reuseFailAlloc_3037_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3036_;
            }
            7 => {
                if v_isShared_3045_ == 0 {
                    v___x_3047_ = v___x_3044_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
                    v___x_3047_ = v_reuseFailAlloc_3048_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3047_;
            }
            9 => {
                v___x_3055_ =
                    l_Lean_IR_ToIR_lowerCode(v_code_3051_, v_a_3009_, v_a_3010_, v_a_3011_);
                if lean_obj_tag(v___x_3055_) == 0 {
                    v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
                    v_isSharedCheck_3066_ = (!lean_is_exclusive(v___x_3055_)) as u8;
                    if v_isSharedCheck_3066_ == 0 {
                        v___x_3058_ = v___x_3055_;
                        v_isShared_3059_ = v_isSharedCheck_3066_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3056_);
                        lean_dec(v___x_3055_);
                        v___x_3058_ = lean_box(0);
                        v_isShared_3059_ = v_isSharedCheck_3066_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3053_);
                    v_a_3067_ = lean_ctor_get(v___x_3055_, 0);
                    v_isSharedCheck_3074_ = (!lean_is_exclusive(v___x_3055_)) as u8;
                    if v_isSharedCheck_3074_ == 0 {
                        v___x_3069_ = v___x_3055_;
                        v_isShared_3070_ = v_isSharedCheck_3074_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3067_);
                        lean_dec(v___x_3055_);
                        v___x_3069_ = lean_box(0);
                        v_isShared_3070_ = v_isSharedCheck_3074_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_3054_ == 0 {
                    lean_ctor_set_tag(v___x_3053_, 1);
                    lean_ctor_set(v___x_3053_, 0, v_a_3056_);
                    v___x_3061_ = v___x_3053_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3056_);
                    v___x_3061_ = v_reuseFailAlloc_3065_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3059_ == 0 {
                    lean_ctor_set(v___x_3058_, 0, v___x_3061_);
                    v___x_3063_ = v___x_3058_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
                    v___x_3063_ = v_reuseFailAlloc_3064_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3063_;
            }
            13 => {
                if v_isShared_3070_ == 0 {
                    v___x_3072_ = v___x_3069_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
                    v___x_3072_ = v_reuseFailAlloc_3073_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(
    mut v_sz_3076_: usize,
    mut v_i_3077_: usize,
    mut v_bs_3078_: *mut LeanObject,
    mut v___y_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
    mut v___y_3081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3083_: u8 = 0;
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: usize = 0;
    let mut v___x_3091_: usize = 0;
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3083_ = lean_usize_dec_lt(v_i_3077_, v_sz_3076_);
                if v___x_3083_ == 0 {
                    v___x_3084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3084_, 0, v_bs_3078_);
                    return v___x_3084_;
                } else {
                    v_v_3085_ = lean_array_uget_borrowed(v_bs_3078_, v_i_3077_);
                    lean_inc(v_v_3085_);
                    v___x_3086_ =
                        l_Lean_IR_ToIR_lowerAlt(v_v_3085_, v___y_3079_, v___y_3080_, v___y_3081_);
                    if lean_obj_tag(v___x_3086_) == 0 {
                        v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
                        lean_inc(v_a_3087_);
                        lean_dec_ref_known(v___x_3086_, 1);
                        v___x_3088_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3089_ = lean_array_uset(v_bs_3078_, v_i_3077_, v___x_3088_);
                        v___x_3090_ = 1usize;
                        v___x_3091_ = lean_usize_add(v_i_3077_, v___x_3090_);
                        v___x_3092_ = lean_array_uset(v_bs_x27_3089_, v_i_3077_, v_a_3087_);
                        v_i_3077_ = v___x_3091_;
                        v_bs_3078_ = v___x_3092_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3078_);
                        v_a_3094_ = lean_ctor_get(v___x_3086_, 0);
                        v_isSharedCheck_3101_ = (!lean_is_exclusive(v___x_3086_)) as u8;
                        if v_isSharedCheck_3101_ == 0 {
                            v___x_3096_ = v___x_3086_;
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3094_);
                            lean_dec(v___x_3086_);
                            v___x_3096_ = lean_box(0);
                            v_isShared_3097_ = v_isSharedCheck_3101_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3097_ == 0 {
                    v___x_3099_ = v___x_3096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__5() -> *mut LeanObject {
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    v___x_3103_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3104_ = lean_unsigned_to_nat(53);
    v___x_3105_ = lean_unsigned_to_nat(95);
    v___x_3106_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3107_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3108_ = l_mkPanicMessageWithDecl(
        v___x_3107_,
        v___x_3106_,
        v___x_3105_,
        v___x_3104_,
        v___x_3103_,
    );
    return v___x_3108_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__6() -> *mut LeanObject {
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    v___x_3109_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3110_ = lean_unsigned_to_nat(44);
    v___x_3111_ = lean_unsigned_to_nat(106);
    v___x_3112_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3113_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3114_ = l_mkPanicMessageWithDecl(
        v___x_3113_,
        v___x_3112_,
        v___x_3111_,
        v___x_3110_,
        v___x_3109_,
    );
    return v___x_3114_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__7() -> *mut LeanObject {
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3116_ = lean_unsigned_to_nat(44);
    v___x_3117_ = lean_unsigned_to_nat(114);
    v___x_3118_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3119_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3120_ = l_mkPanicMessageWithDecl(
        v___x_3119_,
        v___x_3118_,
        v___x_3117_,
        v___x_3116_,
        v___x_3115_,
    );
    return v___x_3120_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__8() -> *mut LeanObject {
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    v___x_3121_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3122_ = lean_unsigned_to_nat(34);
    v___x_3123_ = lean_unsigned_to_nat(113);
    v___x_3124_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3125_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3126_ = l_mkPanicMessageWithDecl(
        v___x_3125_,
        v___x_3124_,
        v___x_3123_,
        v___x_3122_,
        v___x_3121_,
    );
    return v___x_3126_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__9() -> *mut LeanObject {
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    v___x_3127_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3128_ = lean_unsigned_to_nat(44);
    v___x_3129_ = lean_unsigned_to_nat(110);
    v___x_3130_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3131_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3132_ = l_mkPanicMessageWithDecl(
        v___x_3131_,
        v___x_3130_,
        v___x_3129_,
        v___x_3128_,
        v___x_3127_,
    );
    return v___x_3132_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__10() -> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    v___x_3133_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3134_ = lean_unsigned_to_nat(34);
    v___x_3135_ = lean_unsigned_to_nat(109);
    v___x_3136_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3137_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3138_ = l_mkPanicMessageWithDecl(
        v___x_3137_,
        v___x_3136_,
        v___x_3135_,
        v___x_3134_,
        v___x_3133_,
    );
    return v___x_3138_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__11() -> *mut LeanObject {
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    v___x_3139_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3140_ = lean_unsigned_to_nat(41);
    v___x_3141_ = lean_unsigned_to_nat(117);
    v___x_3142_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3143_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3144_ = l_mkPanicMessageWithDecl(
        v___x_3143_,
        v___x_3142_,
        v___x_3141_,
        v___x_3140_,
        v___x_3139_,
    );
    return v___x_3144_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__12() -> *mut LeanObject {
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    v___x_3145_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3146_ = lean_unsigned_to_nat(41);
    v___x_3147_ = lean_unsigned_to_nat(120);
    v___x_3148_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3149_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3150_ = l_mkPanicMessageWithDecl(
        v___x_3149_,
        v___x_3148_,
        v___x_3147_,
        v___x_3146_,
        v___x_3145_,
    );
    return v___x_3150_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__13() -> *mut LeanObject {
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    v___x_3151_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3152_ = lean_unsigned_to_nat(41);
    v___x_3153_ = lean_unsigned_to_nat(123);
    v___x_3154_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3155_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3156_ = l_mkPanicMessageWithDecl(
        v___x_3155_,
        v___x_3154_,
        v___x_3153_,
        v___x_3152_,
        v___x_3151_,
    );
    return v___x_3156_;
}
pub unsafe fn _init_l_Lean_IR_ToIR_lowerCode___closed__14() -> *mut LeanObject {
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    v___x_3157_ = l_Lean_IR_ToIR_lowerCode___closed__4;
    v___x_3158_ = lean_unsigned_to_nat(41);
    v___x_3159_ = lean_unsigned_to_nat(126);
    v___x_3160_ = l_Lean_IR_ToIR_lowerCode___closed__1;
    v___x_3161_ = l_Lean_IR_ToIR_lowerCode___closed__0;
    v___x_3162_ = l_mkPanicMessageWithDecl(
        v___x_3161_,
        v___x_3160_,
        v___x_3159_,
        v___x_3158_,
        v___x_3157_,
    );
    return v___x_3162_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerCode(
    mut v_c_3163_: *mut LeanObject,
    mut v_a_3164_: *mut LeanObject,
    mut v_a_3165_: *mut LeanObject,
    mut v_a_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3180_: usize = 0;
    let mut v___x_3181_: usize = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3195_: u8 = 0;
    let mut v_a_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3199_: u8 = 0;
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v_a_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3207_: u8 = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3211_: u8 = 0;
    let mut v_fvarId_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3219_: usize = 0;
    let mut v___x_3220_: usize = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v_a_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3244_: u8 = 0;
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_isSharedCheck_3249_: u8 = 0;
    let mut v_cases_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3260_: usize = 0;
    let mut v___x_3261_: usize = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3266_: u8 = 0;
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3274_: u8 = 0;
    let mut v_a_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3278_: u8 = 0;
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_isSharedCheck_3293_: u8 = 0;
    let mut v_unused_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3303_: u8 = 0;
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3310_: u8 = 0;
    let mut v_a_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3314_: u8 = 0;
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3322_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut v_unused_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3335_: u8 = 0;
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3345_: u8 = 0;
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3358_: u8 = 0;
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3362_: u8 = 0;
    let mut v_a_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3366_: u8 = 0;
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut v_isSharedCheck_3371_: u8 = 0;
    let mut v_fvarId_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3402_: u8 = 0;
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3406_: u8 = 0;
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3412_: u8 = 0;
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut v_isSharedCheck_3417_: u8 = 0;
    let mut v_fvarId_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3426_: u8 = 0;
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3437_: u8 = 0;
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3445_: u8 = 0;
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3461_: u8 = 0;
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_isSharedCheck_3466_: u8 = 0;
    let mut v_fvarId_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3487_: u8 = 0;
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut v_isSharedCheck_3498_: u8 = 0;
    let mut v_fvarId_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_3501_: u8 = 0;
    let mut v_persistent_3502_: u8 = 0;
    let mut v_k_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3506_: u8 = 0;
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3521_: u8 = 0;
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_isSharedCheck_3532_: u8 = 0;
    let mut v_fvarId_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_check_3535_: u8 = 0;
    let mut v_persistent_3536_: u8 = 0;
    let mut v_k_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_fvarId_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3586_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_c_3163_) {
                0 => {
                    v_decl_3168_ = lean_ctor_get(v_c_3163_, 0);
                    lean_inc_ref(v_decl_3168_);
                    v_k_3169_ = lean_ctor_get(v_c_3163_, 1);
                    lean_inc_ref(v_k_3169_);
                    lean_dec_ref_known(v_c_3163_, 2);
                    v___x_3170_ = l_Lean_IR_ToIR_lowerLet(
                        v_decl_3168_,
                        v_k_3169_,
                        v_a_3164_,
                        v_a_3165_,
                        v_a_3166_,
                    );
                    return v___x_3170_;
                }
                1 => {
                    lean_dec_ref_known(v_c_3163_, 2);
                    v___x_3171_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__3_once),
                        _init_l_Lean_IR_ToIR_lowerCode___closed__3,
                    );
                    v___x_3172_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                        v___x_3171_,
                        v_a_3164_,
                        v_a_3165_,
                        v_a_3166_,
                    );
                    return v___x_3172_;
                }
                2 => {
                    v_decl_3173_ = lean_ctor_get(v_c_3163_, 0);
                    lean_inc_ref(v_decl_3173_);
                    v_k_3174_ = lean_ctor_get(v_c_3163_, 1);
                    lean_inc_ref(v_k_3174_);
                    lean_dec_ref_known(v_c_3163_, 2);
                    v_fvarId_3175_ = lean_ctor_get(v_decl_3173_, 0);
                    lean_inc(v_fvarId_3175_);
                    v_params_3176_ = lean_ctor_get(v_decl_3173_, 2);
                    lean_inc_ref(v_params_3176_);
                    v_value_3177_ = lean_ctor_get(v_decl_3173_, 4);
                    lean_inc_ref(v_value_3177_);
                    lean_dec_ref(v_decl_3173_);
                    v___x_3178_ = l_Lean_IR_ToIR_bindJoinPoint___redArg(v_fvarId_3175_, v_a_3164_);
                    if lean_obj_tag(v___x_3178_) == 0 {
                        v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
                        lean_inc(v_a_3179_);
                        lean_dec_ref_known(v___x_3178_, 1);
                        v_sz_3180_ = lean_array_size(v_params_3176_);
                        v___x_3181_ = 0usize;
                        v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_3180_, v___x_3181_, v_params_3176_, v_a_3164_);
                        if lean_obj_tag(v___x_3182_) == 0 {
                            v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
                            lean_inc(v_a_3183_);
                            lean_dec_ref_known(v___x_3182_, 1);
                            v___x_3184_ = l_Lean_IR_ToIR_lowerCode(
                                v_value_3177_,
                                v_a_3164_,
                                v_a_3165_,
                                v_a_3166_,
                            );
                            if lean_obj_tag(v___x_3184_) == 0 {
                                v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
                                lean_inc(v_a_3185_);
                                lean_dec_ref_known(v___x_3184_, 1);
                                v___x_3186_ = l_Lean_IR_ToIR_lowerCode(
                                    v_k_3174_, v_a_3164_, v_a_3165_, v_a_3166_,
                                );
                                if lean_obj_tag(v___x_3186_) == 0 {
                                    v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
                                    v_isSharedCheck_3195_ = (!lean_is_exclusive(v___x_3186_)) as u8;
                                    if v_isSharedCheck_3195_ == 0 {
                                        v___x_3189_ = v___x_3186_;
                                        v_isShared_3190_ = v_isSharedCheck_3195_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3187_);
                                        lean_dec(v___x_3186_);
                                        v___x_3189_ = lean_box(0);
                                        v_isShared_3190_ = v_isSharedCheck_3195_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3185_);
                                    lean_dec(v_a_3183_);
                                    lean_dec(v_a_3179_);
                                    return v___x_3186_;
                                }
                            } else {
                                lean_dec(v_a_3183_);
                                lean_dec(v_a_3179_);
                                lean_dec_ref(v_k_3174_);
                                return v___x_3184_;
                            }
                        } else {
                            lean_dec(v_a_3179_);
                            lean_dec_ref(v_value_3177_);
                            lean_dec_ref(v_k_3174_);
                            v_a_3196_ = lean_ctor_get(v___x_3182_, 0);
                            v_isSharedCheck_3203_ = (!lean_is_exclusive(v___x_3182_)) as u8;
                            if v_isSharedCheck_3203_ == 0 {
                                v___x_3198_ = v___x_3182_;
                                v_isShared_3199_ = v_isSharedCheck_3203_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3196_);
                                lean_dec(v___x_3182_);
                                v___x_3198_ = lean_box(0);
                                v_isShared_3199_ = v_isSharedCheck_3203_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_value_3177_);
                        lean_dec_ref(v_params_3176_);
                        lean_dec_ref(v_k_3174_);
                        v_a_3204_ = lean_ctor_get(v___x_3178_, 0);
                        v_isSharedCheck_3211_ = (!lean_is_exclusive(v___x_3178_)) as u8;
                        if v_isSharedCheck_3211_ == 0 {
                            v___x_3206_ = v___x_3178_;
                            v_isShared_3207_ = v_isSharedCheck_3211_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3204_);
                            lean_dec(v___x_3178_);
                            v___x_3206_ = lean_box(0);
                            v_isShared_3207_ = v_isSharedCheck_3211_;
                            state = 5;
                            continue;
                        }
                    }
                }
                3 => {
                    v_fvarId_3212_ = lean_ctor_get(v_c_3163_, 0);
                    v_args_3213_ = lean_ctor_get(v_c_3163_, 1);
                    v_isSharedCheck_3249_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3249_ == 0 {
                        v___x_3215_ = v_c_3163_;
                        v_isShared_3216_ = v_isSharedCheck_3249_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_args_3213_);
                        lean_inc(v_fvarId_3212_);
                        lean_dec(v_c_3163_);
                        v___x_3215_ = lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3249_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_cases_3250_ = lean_ctor_get(v_c_3163_, 0);
                    lean_inc_ref(v_cases_3250_);
                    lean_dec_ref_known(v_c_3163_, 1);
                    v_typeName_3251_ = lean_ctor_get(v_cases_3250_, 0);
                    v_discr_3252_ = lean_ctor_get(v_cases_3250_, 2);
                    v_alts_3253_ = lean_ctor_get(v_cases_3250_, 3);
                    v_isSharedCheck_3293_ = (!lean_is_exclusive(v_cases_3250_)) as u8;
                    if v_isSharedCheck_3293_ == 0 {
                        v_unused_3294_ = lean_ctor_get(v_cases_3250_, 1);
                        lean_dec(v_unused_3294_);
                        v___x_3255_ = v_cases_3250_;
                        v_isShared_3256_ = v_isSharedCheck_3293_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_alts_3253_);
                        lean_inc(v_discr_3252_);
                        lean_inc(v_typeName_3251_);
                        lean_dec(v_cases_3250_);
                        v___x_3255_ = lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3293_;
                        state = 15;
                        continue;
                    }
                }
                5 => {
                    v_fvarId_3295_ = lean_ctor_get(v_c_3163_, 0);
                    v_isSharedCheck_3319_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3297_ = v_c_3163_;
                        v_isShared_3298_ = v_isSharedCheck_3319_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_fvarId_3295_);
                        lean_dec(v_c_3163_);
                        v___x_3297_ = lean_box(0);
                        v_isShared_3298_ = v_isSharedCheck_3319_;
                        state = 23;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_3327_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3327_ == 0 {
                        v_unused_3328_ = lean_ctor_get(v_c_3163_, 0);
                        lean_dec(v_unused_3328_);
                        v___x_3321_ = v_c_3163_;
                        v_isShared_3322_ = v_isSharedCheck_3327_;
                        state = 29;
                        continue;
                    } else {
                        lean_dec(v_c_3163_);
                        v___x_3321_ = lean_box(0);
                        v_isShared_3322_ = v_isSharedCheck_3327_;
                        state = 29;
                        continue;
                    }
                }
                7 => {
                    v_fvarId_3329_ = lean_ctor_get(v_c_3163_, 0);
                    v_i_3330_ = lean_ctor_get(v_c_3163_, 1);
                    v_y_3331_ = lean_ctor_get(v_c_3163_, 2);
                    v_k_3332_ = lean_ctor_get(v_c_3163_, 3);
                    v_isSharedCheck_3371_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3371_ == 0 {
                        v___x_3334_ = v_c_3163_;
                        v_isShared_3335_ = v_isSharedCheck_3371_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_k_3332_);
                        lean_inc(v_y_3331_);
                        lean_inc(v_i_3330_);
                        lean_inc(v_fvarId_3329_);
                        lean_dec(v_c_3163_);
                        v___x_3334_ = lean_box(0);
                        v_isShared_3335_ = v_isSharedCheck_3371_;
                        state = 31;
                        continue;
                    }
                }
                8 => {
                    v_fvarId_3372_ = lean_ctor_get(v_c_3163_, 0);
                    v_i_3373_ = lean_ctor_get(v_c_3163_, 1);
                    v_y_3374_ = lean_ctor_get(v_c_3163_, 2);
                    v_k_3375_ = lean_ctor_get(v_c_3163_, 3);
                    v_isSharedCheck_3417_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3417_ == 0 {
                        v___x_3377_ = v_c_3163_;
                        v_isShared_3378_ = v_isSharedCheck_3417_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_k_3375_);
                        lean_inc(v_y_3374_);
                        lean_inc(v_i_3373_);
                        lean_inc(v_fvarId_3372_);
                        lean_dec(v_c_3163_);
                        v___x_3377_ = lean_box(0);
                        v_isShared_3378_ = v_isSharedCheck_3417_;
                        state = 39;
                        continue;
                    }
                }
                9 => {
                    v_fvarId_3418_ = lean_ctor_get(v_c_3163_, 0);
                    v_i_3419_ = lean_ctor_get(v_c_3163_, 1);
                    v_offset_3420_ = lean_ctor_get(v_c_3163_, 2);
                    v_y_3421_ = lean_ctor_get(v_c_3163_, 3);
                    v_ty_3422_ = lean_ctor_get(v_c_3163_, 4);
                    v_k_3423_ = lean_ctor_get(v_c_3163_, 5);
                    v_isSharedCheck_3466_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3466_ == 0 {
                        v___x_3425_ = v_c_3163_;
                        v_isShared_3426_ = v_isSharedCheck_3466_;
                        state = 47;
                        continue;
                    } else {
                        lean_inc(v_k_3423_);
                        lean_inc(v_ty_3422_);
                        lean_inc(v_y_3421_);
                        lean_inc(v_offset_3420_);
                        lean_inc(v_i_3419_);
                        lean_inc(v_fvarId_3418_);
                        lean_dec(v_c_3163_);
                        v___x_3425_ = lean_box(0);
                        v_isShared_3426_ = v_isSharedCheck_3466_;
                        state = 47;
                        continue;
                    }
                }
                10 => {
                    v_fvarId_3467_ = lean_ctor_get(v_c_3163_, 0);
                    v_cidx_3468_ = lean_ctor_get(v_c_3163_, 1);
                    v_k_3469_ = lean_ctor_get(v_c_3163_, 2);
                    v_isSharedCheck_3498_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3498_ == 0 {
                        v___x_3471_ = v_c_3163_;
                        v_isShared_3472_ = v_isSharedCheck_3498_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_k_3469_);
                        lean_inc(v_cidx_3468_);
                        lean_inc(v_fvarId_3467_);
                        lean_dec(v_c_3163_);
                        v___x_3471_ = lean_box(0);
                        v_isShared_3472_ = v_isSharedCheck_3498_;
                        state = 55;
                        continue;
                    }
                }
                11 => {
                    v_fvarId_3499_ = lean_ctor_get(v_c_3163_, 0);
                    v_n_3500_ = lean_ctor_get(v_c_3163_, 1);
                    v_check_3501_ = lean_ctor_get_uint8(
                        v_c_3163_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_3502_ = lean_ctor_get_uint8(
                        v_c_3163_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_k_3503_ = lean_ctor_get(v_c_3163_, 2);
                    v_isSharedCheck_3532_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3532_ == 0 {
                        v___x_3505_ = v_c_3163_;
                        v_isShared_3506_ = v_isSharedCheck_3532_;
                        state = 61;
                        continue;
                    } else {
                        lean_inc(v_k_3503_);
                        lean_inc(v_n_3500_);
                        lean_inc(v_fvarId_3499_);
                        lean_dec(v_c_3163_);
                        v___x_3505_ = lean_box(0);
                        v_isShared_3506_ = v_isSharedCheck_3532_;
                        state = 61;
                        continue;
                    }
                }
                12 => {
                    v_fvarId_3533_ = lean_ctor_get(v_c_3163_, 0);
                    lean_inc(v_fvarId_3533_);
                    v_n_3534_ = lean_ctor_get(v_c_3163_, 1);
                    lean_inc(v_n_3534_);
                    v_check_3535_ = lean_ctor_get_uint8(
                        v_c_3163_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    );
                    v_persistent_3536_ = lean_ctor_get_uint8(
                        v_c_3163_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                    );
                    v_k_3537_ = lean_ctor_get(v_c_3163_, 3);
                    lean_inc_ref(v_k_3537_);
                    lean_dec_ref_known(v_c_3163_, 4);
                    v___x_3538_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3533_, v_a_3164_);
                    lean_dec(v_fvarId_3533_);
                    if lean_obj_tag(v___x_3538_) == 0 {
                        v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
                        lean_inc(v_a_3539_);
                        lean_dec_ref_known(v___x_3538_, 1);
                        if lean_obj_tag(v_a_3539_) == 0 {
                            v_id_3540_ = lean_ctor_get(v_a_3539_, 0);
                            lean_inc(v_id_3540_);
                            lean_dec_ref_known(v_a_3539_, 1);
                            v___x_3541_ = l_Lean_IR_ToIR_lowerCode(
                                v_k_3537_, v_a_3164_, v_a_3165_, v_a_3166_,
                            );
                            if lean_obj_tag(v___x_3541_) == 0 {
                                v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
                                v_isSharedCheck_3550_ = (!lean_is_exclusive(v___x_3541_)) as u8;
                                if v_isSharedCheck_3550_ == 0 {
                                    v___x_3544_ = v___x_3541_;
                                    v_isShared_3545_ = v_isSharedCheck_3550_;
                                    state = 67;
                                    continue;
                                } else {
                                    lean_inc(v_a_3542_);
                                    lean_dec(v___x_3541_);
                                    v___x_3544_ = lean_box(0);
                                    v_isShared_3545_ = v_isSharedCheck_3550_;
                                    state = 67;
                                    continue;
                                }
                            } else {
                                lean_dec(v_id_3540_);
                                lean_dec(v_n_3534_);
                                return v___x_3541_;
                            }
                        } else {
                            lean_dec(v_a_3539_);
                            lean_dec_ref(v_k_3537_);
                            lean_dec(v_n_3534_);
                            v___x_3551_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__13),
                                core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__13_once),
                                _init_l_Lean_IR_ToIR_lowerCode___closed__13,
                            );
                            v___x_3552_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                                v___x_3551_,
                                v_a_3164_,
                                v_a_3165_,
                                v_a_3166_,
                            );
                            return v___x_3552_;
                        }
                    } else {
                        lean_dec_ref(v_k_3537_);
                        lean_dec(v_n_3534_);
                        v_a_3553_ = lean_ctor_get(v___x_3538_, 0);
                        v_isSharedCheck_3560_ = (!lean_is_exclusive(v___x_3538_)) as u8;
                        if v_isSharedCheck_3560_ == 0 {
                            v___x_3555_ = v___x_3538_;
                            v_isShared_3556_ = v_isSharedCheck_3560_;
                            state = 69;
                            continue;
                        } else {
                            lean_inc(v_a_3553_);
                            lean_dec(v___x_3538_);
                            v___x_3555_ = lean_box(0);
                            v_isShared_3556_ = v_isSharedCheck_3560_;
                            state = 69;
                            continue;
                        }
                    }
                }
                _ => {
                    v_fvarId_3561_ = lean_ctor_get(v_c_3163_, 0);
                    v_k_3562_ = lean_ctor_get(v_c_3163_, 1);
                    v_isSharedCheck_3591_ = (!lean_is_exclusive(v_c_3163_)) as u8;
                    if v_isSharedCheck_3591_ == 0 {
                        v___x_3564_ = v_c_3163_;
                        v_isShared_3565_ = v_isSharedCheck_3591_;
                        state = 71;
                        continue;
                    } else {
                        lean_inc(v_k_3562_);
                        lean_inc(v_fvarId_3561_);
                        lean_dec(v_c_3163_);
                        v___x_3564_ = lean_box(0);
                        v_isShared_3565_ = v_isSharedCheck_3591_;
                        state = 71;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3191_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_3191_, 0, v_a_3179_);
                lean_ctor_set(v___x_3191_, 1, v_a_3183_);
                lean_ctor_set(v___x_3191_, 2, v_a_3185_);
                lean_ctor_set(v___x_3191_, 3, v_a_3187_);
                if v_isShared_3190_ == 0 {
                    lean_ctor_set(v___x_3189_, 0, v___x_3191_);
                    v___x_3193_ = v___x_3189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3191_);
                    v___x_3193_ = v_reuseFailAlloc_3194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3193_;
            }
            3 => {
                if v_isShared_3199_ == 0 {
                    v___x_3201_ = v___x_3198_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
                    v___x_3201_ = v_reuseFailAlloc_3202_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3201_;
            }
            5 => {
                if v_isShared_3207_ == 0 {
                    v___x_3209_ = v___x_3206_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
                    v___x_3209_ = v_reuseFailAlloc_3210_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3209_;
            }
            7 => {
                v___x_3217_ = l_Lean_IR_ToIR_getJoinPointValue___redArg(v_fvarId_3212_, v_a_3164_);
                lean_dec(v_fvarId_3212_);
                if lean_obj_tag(v___x_3217_) == 0 {
                    v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
                    lean_inc(v_a_3218_);
                    lean_dec_ref_known(v___x_3217_, 1);
                    v_sz_3219_ = lean_array_size(v_args_3213_);
                    v___x_3220_ = 0usize;
                    v___x_3221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_3219_, v___x_3220_, v_args_3213_, v_a_3164_);
                    if lean_obj_tag(v___x_3221_) == 0 {
                        v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
                        v_isSharedCheck_3232_ = (!lean_is_exclusive(v___x_3221_)) as u8;
                        if v_isSharedCheck_3232_ == 0 {
                            v___x_3224_ = v___x_3221_;
                            v_isShared_3225_ = v_isSharedCheck_3232_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3222_);
                            lean_dec(v___x_3221_);
                            v___x_3224_ = lean_box(0);
                            v_isShared_3225_ = v_isSharedCheck_3232_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3218_);
                        lean_del_object(v___x_3215_);
                        v_a_3233_ = lean_ctor_get(v___x_3221_, 0);
                        v_isSharedCheck_3240_ = (!lean_is_exclusive(v___x_3221_)) as u8;
                        if v_isSharedCheck_3240_ == 0 {
                            v___x_3235_ = v___x_3221_;
                            v_isShared_3236_ = v_isSharedCheck_3240_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3233_);
                            lean_dec(v___x_3221_);
                            v___x_3235_ = lean_box(0);
                            v_isShared_3236_ = v_isSharedCheck_3240_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3215_);
                    lean_dec_ref(v_args_3213_);
                    v_a_3241_ = lean_ctor_get(v___x_3217_, 0);
                    v_isSharedCheck_3248_ = (!lean_is_exclusive(v___x_3217_)) as u8;
                    if v_isSharedCheck_3248_ == 0 {
                        v___x_3243_ = v___x_3217_;
                        v_isShared_3244_ = v_isSharedCheck_3248_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3241_);
                        lean_dec(v___x_3217_);
                        v___x_3243_ = lean_box(0);
                        v_isShared_3244_ = v_isSharedCheck_3248_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_3216_ == 0 {
                    lean_ctor_set_tag(v___x_3215_, 11);
                    lean_ctor_set(v___x_3215_, 1, v_a_3222_);
                    lean_ctor_set(v___x_3215_, 0, v_a_3218_);
                    v___x_3227_ = v___x_3215_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(11, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3218_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_a_3222_);
                    v___x_3227_ = v_reuseFailAlloc_3231_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3225_ == 0 {
                    lean_ctor_set(v___x_3224_, 0, v___x_3227_);
                    v___x_3229_ = v___x_3224_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
                    v___x_3229_ = v_reuseFailAlloc_3230_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3229_;
            }
            11 => {
                if v_isShared_3236_ == 0 {
                    v___x_3238_ = v___x_3235_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
                    v___x_3238_ = v_reuseFailAlloc_3239_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3238_;
            }
            13 => {
                if v_isShared_3244_ == 0 {
                    v___x_3246_ = v___x_3243_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
                    v___x_3246_ = v_reuseFailAlloc_3247_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3246_;
            }
            15 => {
                v___x_3257_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_discr_3252_, v_a_3164_);
                lean_dec(v_discr_3252_);
                if lean_obj_tag(v___x_3257_) == 0 {
                    v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
                    lean_inc(v_a_3258_);
                    lean_dec_ref_known(v___x_3257_, 1);
                    if lean_obj_tag(v_a_3258_) == 0 {
                        v_id_3259_ = lean_ctor_get(v_a_3258_, 0);
                        lean_inc(v_id_3259_);
                        lean_dec_ref_known(v_a_3258_, 1);
                        v_sz_3260_ = lean_array_size(v_alts_3253_);
                        v___x_3261_ = 0usize;
                        v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_3260_, v___x_3261_, v_alts_3253_, v_a_3164_, v_a_3165_, v_a_3166_);
                        if lean_obj_tag(v___x_3262_) == 0 {
                            v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
                            v_isSharedCheck_3274_ = (!lean_is_exclusive(v___x_3262_)) as u8;
                            if v_isSharedCheck_3274_ == 0 {
                                v___x_3265_ = v___x_3262_;
                                v_isShared_3266_ = v_isSharedCheck_3274_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_3263_);
                                lean_dec(v___x_3262_);
                                v___x_3265_ = lean_box(0);
                                v_isShared_3266_ = v_isSharedCheck_3274_;
                                state = 16;
                                continue;
                            }
                        } else {
                            lean_dec(v_id_3259_);
                            lean_del_object(v___x_3255_);
                            lean_dec(v_typeName_3251_);
                            v_a_3275_ = lean_ctor_get(v___x_3262_, 0);
                            v_isSharedCheck_3282_ = (!lean_is_exclusive(v___x_3262_)) as u8;
                            if v_isSharedCheck_3282_ == 0 {
                                v___x_3277_ = v___x_3262_;
                                v_isShared_3278_ = v_isSharedCheck_3282_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_3275_);
                                lean_dec(v___x_3262_);
                                v___x_3277_ = lean_box(0);
                                v_isShared_3278_ = v_isSharedCheck_3282_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3258_);
                        lean_del_object(v___x_3255_);
                        lean_dec_ref(v_alts_3253_);
                        lean_dec(v_typeName_3251_);
                        v___x_3283_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__5_once),
                            _init_l_Lean_IR_ToIR_lowerCode___closed__5,
                        );
                        v___x_3284_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                            v___x_3283_,
                            v_a_3164_,
                            v_a_3165_,
                            v_a_3166_,
                        );
                        return v___x_3284_;
                    }
                } else {
                    lean_del_object(v___x_3255_);
                    lean_dec_ref(v_alts_3253_);
                    lean_dec(v_typeName_3251_);
                    v_a_3285_ = lean_ctor_get(v___x_3257_, 0);
                    v_isSharedCheck_3292_ = (!lean_is_exclusive(v___x_3257_)) as u8;
                    if v_isSharedCheck_3292_ == 0 {
                        v___x_3287_ = v___x_3257_;
                        v_isShared_3288_ = v_isSharedCheck_3292_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3285_);
                        lean_dec(v___x_3257_);
                        v___x_3287_ = lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3292_;
                        state = 21;
                        continue;
                    }
                }
            }
            16 => {
                v___x_3267_ = l_Lean_IR_nameToIRType(v_typeName_3251_);
                if v_isShared_3256_ == 0 {
                    lean_ctor_set_tag(v___x_3255_, 9);
                    lean_ctor_set(v___x_3255_, 3, v_a_3263_);
                    lean_ctor_set(v___x_3255_, 2, v___x_3267_);
                    lean_ctor_set(v___x_3255_, 1, v_id_3259_);
                    v___x_3269_ = v___x_3255_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3273_ = lean_alloc_ctor(9, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_typeName_3251_);
                    lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_id_3259_);
                    lean_ctor_set(v_reuseFailAlloc_3273_, 2, v___x_3267_);
                    lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_a_3263_);
                    v___x_3269_ = v_reuseFailAlloc_3273_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_3266_ == 0 {
                    lean_ctor_set(v___x_3265_, 0, v___x_3269_);
                    v___x_3271_ = v___x_3265_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3269_);
                    v___x_3271_ = v_reuseFailAlloc_3272_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3271_;
            }
            19 => {
                if v_isShared_3278_ == 0 {
                    v___x_3280_ = v___x_3277_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
                    v___x_3280_ = v_reuseFailAlloc_3281_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3280_;
            }
            21 => {
                if v_isShared_3288_ == 0 {
                    v___x_3290_ = v___x_3287_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
                    v___x_3290_ = v_reuseFailAlloc_3291_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3290_;
            }
            23 => {
                v___x_3299_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3295_, v_a_3164_);
                lean_dec(v_fvarId_3295_);
                if lean_obj_tag(v___x_3299_) == 0 {
                    v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
                    v_isSharedCheck_3310_ = (!lean_is_exclusive(v___x_3299_)) as u8;
                    if v_isSharedCheck_3310_ == 0 {
                        v___x_3302_ = v___x_3299_;
                        v_isShared_3303_ = v_isSharedCheck_3310_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_3300_);
                        lean_dec(v___x_3299_);
                        v___x_3302_ = lean_box(0);
                        v_isShared_3303_ = v_isSharedCheck_3310_;
                        state = 24;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3297_);
                    v_a_3311_ = lean_ctor_get(v___x_3299_, 0);
                    v_isSharedCheck_3318_ = (!lean_is_exclusive(v___x_3299_)) as u8;
                    if v_isSharedCheck_3318_ == 0 {
                        v___x_3313_ = v___x_3299_;
                        v_isShared_3314_ = v_isSharedCheck_3318_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_3311_);
                        lean_dec(v___x_3299_);
                        v___x_3313_ = lean_box(0);
                        v_isShared_3314_ = v_isSharedCheck_3318_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_3298_ == 0 {
                    lean_ctor_set_tag(v___x_3297_, 10);
                    lean_ctor_set(v___x_3297_, 0, v_a_3300_);
                    v___x_3305_ = v___x_3297_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = lean_alloc_ctor(10, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3300_);
                    v___x_3305_ = v_reuseFailAlloc_3309_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3303_ == 0 {
                    lean_ctor_set(v___x_3302_, 0, v___x_3305_);
                    v___x_3307_ = v___x_3302_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3305_);
                    v___x_3307_ = v_reuseFailAlloc_3308_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3307_;
            }
            27 => {
                if v_isShared_3314_ == 0 {
                    v___x_3316_ = v___x_3313_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
                    v___x_3316_ = v_reuseFailAlloc_3317_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3316_;
            }
            29 => {
                v___x_3323_ = lean_box(12);
                if v_isShared_3322_ == 0 {
                    lean_ctor_set_tag(v___x_3321_, 0);
                    lean_ctor_set(v___x_3321_, 0, v___x_3323_);
                    v___x_3325_ = v___x_3321_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3323_);
                    v___x_3325_ = v_reuseFailAlloc_3326_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3325_;
            }
            31 => {
                v___x_3336_ = l_Lean_IR_ToIR_lowerArg___redArg(v_y_3331_, v_a_3164_);
                lean_dec(v_y_3331_);
                if lean_obj_tag(v___x_3336_) == 0 {
                    v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
                    lean_inc(v_a_3337_);
                    lean_dec_ref_known(v___x_3336_, 1);
                    v___x_3338_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3329_, v_a_3164_);
                    lean_dec(v_fvarId_3329_);
                    if lean_obj_tag(v___x_3338_) == 0 {
                        v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
                        lean_inc(v_a_3339_);
                        lean_dec_ref_known(v___x_3338_, 1);
                        if lean_obj_tag(v_a_3339_) == 0 {
                            v_id_3340_ = lean_ctor_get(v_a_3339_, 0);
                            lean_inc(v_id_3340_);
                            lean_dec_ref_known(v_a_3339_, 1);
                            v___x_3341_ = l_Lean_IR_ToIR_lowerCode(
                                v_k_3332_, v_a_3164_, v_a_3165_, v_a_3166_,
                            );
                            if lean_obj_tag(v___x_3341_) == 0 {
                                v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
                                v_isSharedCheck_3352_ = (!lean_is_exclusive(v___x_3341_)) as u8;
                                if v_isSharedCheck_3352_ == 0 {
                                    v___x_3344_ = v___x_3341_;
                                    v_isShared_3345_ = v_isSharedCheck_3352_;
                                    state = 32;
                                    continue;
                                } else {
                                    lean_inc(v_a_3342_);
                                    lean_dec(v___x_3341_);
                                    v___x_3344_ = lean_box(0);
                                    v_isShared_3345_ = v_isSharedCheck_3352_;
                                    state = 32;
                                    continue;
                                }
                            } else {
                                lean_dec(v_id_3340_);
                                lean_dec(v_a_3337_);
                                lean_del_object(v___x_3334_);
                                lean_dec(v_i_3330_);
                                return v___x_3341_;
                            }
                        } else {
                            lean_dec(v_a_3339_);
                            lean_dec(v_a_3337_);
                            lean_del_object(v___x_3334_);
                            lean_dec_ref(v_k_3332_);
                            lean_dec(v_i_3330_);
                            v___x_3353_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__6),
                                core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__6_once),
                                _init_l_Lean_IR_ToIR_lowerCode___closed__6,
                            );
                            v___x_3354_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                                v___x_3353_,
                                v_a_3164_,
                                v_a_3165_,
                                v_a_3166_,
                            );
                            return v___x_3354_;
                        }
                    } else {
                        lean_dec(v_a_3337_);
                        lean_del_object(v___x_3334_);
                        lean_dec_ref(v_k_3332_);
                        lean_dec(v_i_3330_);
                        v_a_3355_ = lean_ctor_get(v___x_3338_, 0);
                        v_isSharedCheck_3362_ = (!lean_is_exclusive(v___x_3338_)) as u8;
                        if v_isSharedCheck_3362_ == 0 {
                            v___x_3357_ = v___x_3338_;
                            v_isShared_3358_ = v_isSharedCheck_3362_;
                            state = 35;
                            continue;
                        } else {
                            lean_inc(v_a_3355_);
                            lean_dec(v___x_3338_);
                            v___x_3357_ = lean_box(0);
                            v_isShared_3358_ = v_isSharedCheck_3362_;
                            state = 35;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3334_);
                    lean_dec_ref(v_k_3332_);
                    lean_dec(v_i_3330_);
                    lean_dec(v_fvarId_3329_);
                    v_a_3363_ = lean_ctor_get(v___x_3336_, 0);
                    v_isSharedCheck_3370_ = (!lean_is_exclusive(v___x_3336_)) as u8;
                    if v_isSharedCheck_3370_ == 0 {
                        v___x_3365_ = v___x_3336_;
                        v_isShared_3366_ = v_isSharedCheck_3370_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_a_3363_);
                        lean_dec(v___x_3336_);
                        v___x_3365_ = lean_box(0);
                        v_isShared_3366_ = v_isSharedCheck_3370_;
                        state = 37;
                        continue;
                    }
                }
            }
            32 => {
                if v_isShared_3335_ == 0 {
                    lean_ctor_set_tag(v___x_3334_, 2);
                    lean_ctor_set(v___x_3334_, 3, v_a_3342_);
                    lean_ctor_set(v___x_3334_, 2, v_a_3337_);
                    lean_ctor_set(v___x_3334_, 0, v_id_3340_);
                    v___x_3347_ = v___x_3334_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = lean_alloc_ctor(2, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_id_3340_);
                    lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_i_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3351_, 2, v_a_3337_);
                    lean_ctor_set(v_reuseFailAlloc_3351_, 3, v_a_3342_);
                    v___x_3347_ = v_reuseFailAlloc_3351_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                if v_isShared_3345_ == 0 {
                    lean_ctor_set(v___x_3344_, 0, v___x_3347_);
                    v___x_3349_ = v___x_3344_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
                    v___x_3349_ = v_reuseFailAlloc_3350_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3349_;
            }
            35 => {
                if v_isShared_3358_ == 0 {
                    v___x_3360_ = v___x_3357_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
                    v___x_3360_ = v_reuseFailAlloc_3361_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3360_;
            }
            37 => {
                if v_isShared_3366_ == 0 {
                    v___x_3368_ = v___x_3365_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
                    v___x_3368_ = v_reuseFailAlloc_3369_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3368_;
            }
            39 => {
                v___x_3379_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_3374_, v_a_3164_);
                lean_dec(v_y_3374_);
                if lean_obj_tag(v___x_3379_) == 0 {
                    v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
                    lean_inc(v_a_3380_);
                    lean_dec_ref_known(v___x_3379_, 1);
                    if lean_obj_tag(v_a_3380_) == 0 {
                        v_id_3381_ = lean_ctor_get(v_a_3380_, 0);
                        lean_inc(v_id_3381_);
                        lean_dec_ref_known(v_a_3380_, 1);
                        v___x_3382_ =
                            l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3372_, v_a_3164_);
                        lean_dec(v_fvarId_3372_);
                        if lean_obj_tag(v___x_3382_) == 0 {
                            v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
                            lean_inc(v_a_3383_);
                            lean_dec_ref_known(v___x_3382_, 1);
                            if lean_obj_tag(v_a_3383_) == 0 {
                                v_id_3384_ = lean_ctor_get(v_a_3383_, 0);
                                lean_inc(v_id_3384_);
                                lean_dec_ref_known(v_a_3383_, 1);
                                v___x_3385_ = l_Lean_IR_ToIR_lowerCode(
                                    v_k_3375_, v_a_3164_, v_a_3165_, v_a_3166_,
                                );
                                if lean_obj_tag(v___x_3385_) == 0 {
                                    v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
                                    v_isSharedCheck_3396_ = (!lean_is_exclusive(v___x_3385_)) as u8;
                                    if v_isSharedCheck_3396_ == 0 {
                                        v___x_3388_ = v___x_3385_;
                                        v_isShared_3389_ = v_isSharedCheck_3396_;
                                        state = 40;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3386_);
                                        lean_dec(v___x_3385_);
                                        v___x_3388_ = lean_box(0);
                                        v_isShared_3389_ = v_isSharedCheck_3396_;
                                        state = 40;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_id_3384_);
                                    lean_dec(v_id_3381_);
                                    lean_del_object(v___x_3377_);
                                    lean_dec(v_i_3373_);
                                    return v___x_3385_;
                                }
                            } else {
                                lean_dec(v_a_3383_);
                                lean_dec(v_id_3381_);
                                lean_del_object(v___x_3377_);
                                lean_dec_ref(v_k_3375_);
                                lean_dec(v_i_3373_);
                                v___x_3397_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__7),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_IR_ToIR_lowerCode___closed__7_once
                                    ),
                                    _init_l_Lean_IR_ToIR_lowerCode___closed__7,
                                );
                                v___x_3398_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                                    v___x_3397_,
                                    v_a_3164_,
                                    v_a_3165_,
                                    v_a_3166_,
                                );
                                return v___x_3398_;
                            }
                        } else {
                            lean_dec(v_id_3381_);
                            lean_del_object(v___x_3377_);
                            lean_dec_ref(v_k_3375_);
                            lean_dec(v_i_3373_);
                            v_a_3399_ = lean_ctor_get(v___x_3382_, 0);
                            v_isSharedCheck_3406_ = (!lean_is_exclusive(v___x_3382_)) as u8;
                            if v_isSharedCheck_3406_ == 0 {
                                v___x_3401_ = v___x_3382_;
                                v_isShared_3402_ = v_isSharedCheck_3406_;
                                state = 43;
                                continue;
                            } else {
                                lean_inc(v_a_3399_);
                                lean_dec(v___x_3382_);
                                v___x_3401_ = lean_box(0);
                                v_isShared_3402_ = v_isSharedCheck_3406_;
                                state = 43;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3380_);
                        lean_del_object(v___x_3377_);
                        lean_dec_ref(v_k_3375_);
                        lean_dec(v_i_3373_);
                        lean_dec(v_fvarId_3372_);
                        v___x_3407_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__8),
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__8_once),
                            _init_l_Lean_IR_ToIR_lowerCode___closed__8,
                        );
                        v___x_3408_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                            v___x_3407_,
                            v_a_3164_,
                            v_a_3165_,
                            v_a_3166_,
                        );
                        return v___x_3408_;
                    }
                } else {
                    lean_del_object(v___x_3377_);
                    lean_dec_ref(v_k_3375_);
                    lean_dec(v_i_3373_);
                    lean_dec(v_fvarId_3372_);
                    v_a_3409_ = lean_ctor_get(v___x_3379_, 0);
                    v_isSharedCheck_3416_ = (!lean_is_exclusive(v___x_3379_)) as u8;
                    if v_isSharedCheck_3416_ == 0 {
                        v___x_3411_ = v___x_3379_;
                        v_isShared_3412_ = v_isSharedCheck_3416_;
                        state = 45;
                        continue;
                    } else {
                        lean_inc(v_a_3409_);
                        lean_dec(v___x_3379_);
                        v___x_3411_ = lean_box(0);
                        v_isShared_3412_ = v_isSharedCheck_3416_;
                        state = 45;
                        continue;
                    }
                }
            }
            40 => {
                if v_isShared_3378_ == 0 {
                    lean_ctor_set_tag(v___x_3377_, 4);
                    lean_ctor_set(v___x_3377_, 3, v_a_3386_);
                    lean_ctor_set(v___x_3377_, 2, v_id_3381_);
                    lean_ctor_set(v___x_3377_, 0, v_id_3384_);
                    v___x_3391_ = v___x_3377_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3395_ = lean_alloc_ctor(4, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_id_3384_);
                    lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_i_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_id_3381_);
                    lean_ctor_set(v_reuseFailAlloc_3395_, 3, v_a_3386_);
                    v___x_3391_ = v_reuseFailAlloc_3395_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3389_ == 0 {
                    lean_ctor_set(v___x_3388_, 0, v___x_3391_);
                    v___x_3393_ = v___x_3388_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
                    v___x_3393_ = v_reuseFailAlloc_3394_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3393_;
            }
            43 => {
                if v_isShared_3402_ == 0 {
                    v___x_3404_ = v___x_3401_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
                    v___x_3404_ = v_reuseFailAlloc_3405_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_3404_;
            }
            45 => {
                if v_isShared_3412_ == 0 {
                    v___x_3414_ = v___x_3411_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
                    v___x_3414_ = v_reuseFailAlloc_3415_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3414_;
            }
            47 => {
                v___x_3427_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_y_3421_, v_a_3164_);
                lean_dec(v_y_3421_);
                if lean_obj_tag(v___x_3427_) == 0 {
                    v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
                    lean_inc(v_a_3428_);
                    lean_dec_ref_known(v___x_3427_, 1);
                    if lean_obj_tag(v_a_3428_) == 0 {
                        v_id_3429_ = lean_ctor_get(v_a_3428_, 0);
                        lean_inc(v_id_3429_);
                        lean_dec_ref_known(v_a_3428_, 1);
                        v___x_3430_ =
                            l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3418_, v_a_3164_);
                        lean_dec(v_fvarId_3418_);
                        if lean_obj_tag(v___x_3430_) == 0 {
                            v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
                            lean_inc(v_a_3431_);
                            lean_dec_ref_known(v___x_3430_, 1);
                            if lean_obj_tag(v_a_3431_) == 0 {
                                v_id_3432_ = lean_ctor_get(v_a_3431_, 0);
                                lean_inc(v_id_3432_);
                                lean_dec_ref_known(v_a_3431_, 1);
                                v___x_3433_ = l_Lean_IR_ToIR_lowerCode(
                                    v_k_3423_, v_a_3164_, v_a_3165_, v_a_3166_,
                                );
                                if lean_obj_tag(v___x_3433_) == 0 {
                                    v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
                                    v_isSharedCheck_3445_ = (!lean_is_exclusive(v___x_3433_)) as u8;
                                    if v_isSharedCheck_3445_ == 0 {
                                        v___x_3436_ = v___x_3433_;
                                        v_isShared_3437_ = v_isSharedCheck_3445_;
                                        state = 48;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3434_);
                                        lean_dec(v___x_3433_);
                                        v___x_3436_ = lean_box(0);
                                        v_isShared_3437_ = v_isSharedCheck_3445_;
                                        state = 48;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_id_3432_);
                                    lean_dec(v_id_3429_);
                                    lean_del_object(v___x_3425_);
                                    lean_dec_ref(v_ty_3422_);
                                    lean_dec(v_offset_3420_);
                                    lean_dec(v_i_3419_);
                                    return v___x_3433_;
                                }
                            } else {
                                lean_dec(v_a_3431_);
                                lean_dec(v_id_3429_);
                                lean_del_object(v___x_3425_);
                                lean_dec_ref(v_k_3423_);
                                lean_dec_ref(v_ty_3422_);
                                lean_dec(v_offset_3420_);
                                lean_dec(v_i_3419_);
                                v___x_3446_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__9),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_IR_ToIR_lowerCode___closed__9_once
                                    ),
                                    _init_l_Lean_IR_ToIR_lowerCode___closed__9,
                                );
                                v___x_3447_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                                    v___x_3446_,
                                    v_a_3164_,
                                    v_a_3165_,
                                    v_a_3166_,
                                );
                                return v___x_3447_;
                            }
                        } else {
                            lean_dec(v_id_3429_);
                            lean_del_object(v___x_3425_);
                            lean_dec_ref(v_k_3423_);
                            lean_dec_ref(v_ty_3422_);
                            lean_dec(v_offset_3420_);
                            lean_dec(v_i_3419_);
                            v_a_3448_ = lean_ctor_get(v___x_3430_, 0);
                            v_isSharedCheck_3455_ = (!lean_is_exclusive(v___x_3430_)) as u8;
                            if v_isSharedCheck_3455_ == 0 {
                                v___x_3450_ = v___x_3430_;
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 51;
                                continue;
                            } else {
                                lean_inc(v_a_3448_);
                                lean_dec(v___x_3430_);
                                v___x_3450_ = lean_box(0);
                                v_isShared_3451_ = v_isSharedCheck_3455_;
                                state = 51;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3428_);
                        lean_del_object(v___x_3425_);
                        lean_dec_ref(v_k_3423_);
                        lean_dec_ref(v_ty_3422_);
                        lean_dec(v_offset_3420_);
                        lean_dec(v_i_3419_);
                        lean_dec(v_fvarId_3418_);
                        v___x_3456_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__10),
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__10_once),
                            _init_l_Lean_IR_ToIR_lowerCode___closed__10,
                        );
                        v___x_3457_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                            v___x_3456_,
                            v_a_3164_,
                            v_a_3165_,
                            v_a_3166_,
                        );
                        return v___x_3457_;
                    }
                } else {
                    lean_del_object(v___x_3425_);
                    lean_dec_ref(v_k_3423_);
                    lean_dec_ref(v_ty_3422_);
                    lean_dec(v_offset_3420_);
                    lean_dec(v_i_3419_);
                    lean_dec(v_fvarId_3418_);
                    v_a_3458_ = lean_ctor_get(v___x_3427_, 0);
                    v_isSharedCheck_3465_ = (!lean_is_exclusive(v___x_3427_)) as u8;
                    if v_isSharedCheck_3465_ == 0 {
                        v___x_3460_ = v___x_3427_;
                        v_isShared_3461_ = v_isSharedCheck_3465_;
                        state = 53;
                        continue;
                    } else {
                        lean_inc(v_a_3458_);
                        lean_dec(v___x_3427_);
                        v___x_3460_ = lean_box(0);
                        v_isShared_3461_ = v_isSharedCheck_3465_;
                        state = 53;
                        continue;
                    }
                }
            }
            48 => {
                v___x_3438_ = l_Lean_IR_toIRType(v_ty_3422_);
                lean_dec_ref(v_ty_3422_);
                if v_isShared_3426_ == 0 {
                    lean_ctor_set_tag(v___x_3425_, 5);
                    lean_ctor_set(v___x_3425_, 5, v_a_3434_);
                    lean_ctor_set(v___x_3425_, 4, v___x_3438_);
                    lean_ctor_set(v___x_3425_, 3, v_id_3429_);
                    lean_ctor_set(v___x_3425_, 0, v_id_3432_);
                    v___x_3440_ = v___x_3425_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3444_ = lean_alloc_ctor(5, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_id_3432_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_i_3419_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_offset_3420_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 3, v_id_3429_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 4, v___x_3438_);
                    lean_ctor_set(v_reuseFailAlloc_3444_, 5, v_a_3434_);
                    v___x_3440_ = v_reuseFailAlloc_3444_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_3437_ == 0 {
                    lean_ctor_set(v___x_3436_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3436_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_3442_;
            }
            51 => {
                if v_isShared_3451_ == 0 {
                    v___x_3453_ = v___x_3450_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_3453_;
            }
            53 => {
                if v_isShared_3461_ == 0 {
                    v___x_3463_ = v___x_3460_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
                    v___x_3463_ = v_reuseFailAlloc_3464_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_3463_;
            }
            55 => {
                v___x_3473_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3467_, v_a_3164_);
                lean_dec(v_fvarId_3467_);
                if lean_obj_tag(v___x_3473_) == 0 {
                    v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
                    lean_inc(v_a_3474_);
                    lean_dec_ref_known(v___x_3473_, 1);
                    if lean_obj_tag(v_a_3474_) == 0 {
                        v_id_3475_ = lean_ctor_get(v_a_3474_, 0);
                        lean_inc(v_id_3475_);
                        lean_dec_ref_known(v_a_3474_, 1);
                        v___x_3476_ =
                            l_Lean_IR_ToIR_lowerCode(v_k_3469_, v_a_3164_, v_a_3165_, v_a_3166_);
                        if lean_obj_tag(v___x_3476_) == 0 {
                            v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
                            v_isSharedCheck_3487_ = (!lean_is_exclusive(v___x_3476_)) as u8;
                            if v_isSharedCheck_3487_ == 0 {
                                v___x_3479_ = v___x_3476_;
                                v_isShared_3480_ = v_isSharedCheck_3487_;
                                state = 56;
                                continue;
                            } else {
                                lean_inc(v_a_3477_);
                                lean_dec(v___x_3476_);
                                v___x_3479_ = lean_box(0);
                                v_isShared_3480_ = v_isSharedCheck_3487_;
                                state = 56;
                                continue;
                            }
                        } else {
                            lean_dec(v_id_3475_);
                            lean_del_object(v___x_3471_);
                            lean_dec(v_cidx_3468_);
                            return v___x_3476_;
                        }
                    } else {
                        lean_dec(v_a_3474_);
                        lean_del_object(v___x_3471_);
                        lean_dec_ref(v_k_3469_);
                        lean_dec(v_cidx_3468_);
                        v___x_3488_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__11),
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__11_once),
                            _init_l_Lean_IR_ToIR_lowerCode___closed__11,
                        );
                        v___x_3489_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                            v___x_3488_,
                            v_a_3164_,
                            v_a_3165_,
                            v_a_3166_,
                        );
                        return v___x_3489_;
                    }
                } else {
                    lean_del_object(v___x_3471_);
                    lean_dec_ref(v_k_3469_);
                    lean_dec(v_cidx_3468_);
                    v_a_3490_ = lean_ctor_get(v___x_3473_, 0);
                    v_isSharedCheck_3497_ = (!lean_is_exclusive(v___x_3473_)) as u8;
                    if v_isSharedCheck_3497_ == 0 {
                        v___x_3492_ = v___x_3473_;
                        v_isShared_3493_ = v_isSharedCheck_3497_;
                        state = 59;
                        continue;
                    } else {
                        lean_inc(v_a_3490_);
                        lean_dec(v___x_3473_);
                        v___x_3492_ = lean_box(0);
                        v_isShared_3493_ = v_isSharedCheck_3497_;
                        state = 59;
                        continue;
                    }
                }
            }
            56 => {
                if v_isShared_3472_ == 0 {
                    lean_ctor_set_tag(v___x_3471_, 3);
                    lean_ctor_set(v___x_3471_, 2, v_a_3477_);
                    lean_ctor_set(v___x_3471_, 0, v_id_3475_);
                    v___x_3482_ = v___x_3471_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_3486_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_id_3475_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_cidx_3468_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_a_3477_);
                    v___x_3482_ = v_reuseFailAlloc_3486_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_3480_ == 0 {
                    lean_ctor_set(v___x_3479_, 0, v___x_3482_);
                    v___x_3484_ = v___x_3479_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
                    v___x_3484_ = v_reuseFailAlloc_3485_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_3484_;
            }
            59 => {
                if v_isShared_3493_ == 0 {
                    v___x_3495_ = v___x_3492_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
                    v___x_3495_ = v_reuseFailAlloc_3496_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_3495_;
            }
            61 => {
                v___x_3507_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3499_, v_a_3164_);
                lean_dec(v_fvarId_3499_);
                if lean_obj_tag(v___x_3507_) == 0 {
                    v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
                    lean_inc(v_a_3508_);
                    lean_dec_ref_known(v___x_3507_, 1);
                    if lean_obj_tag(v_a_3508_) == 0 {
                        v_id_3509_ = lean_ctor_get(v_a_3508_, 0);
                        lean_inc(v_id_3509_);
                        lean_dec_ref_known(v_a_3508_, 1);
                        v___x_3510_ =
                            l_Lean_IR_ToIR_lowerCode(v_k_3503_, v_a_3164_, v_a_3165_, v_a_3166_);
                        if lean_obj_tag(v___x_3510_) == 0 {
                            v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
                            v_isSharedCheck_3521_ = (!lean_is_exclusive(v___x_3510_)) as u8;
                            if v_isSharedCheck_3521_ == 0 {
                                v___x_3513_ = v___x_3510_;
                                v_isShared_3514_ = v_isSharedCheck_3521_;
                                state = 62;
                                continue;
                            } else {
                                lean_inc(v_a_3511_);
                                lean_dec(v___x_3510_);
                                v___x_3513_ = lean_box(0);
                                v_isShared_3514_ = v_isSharedCheck_3521_;
                                state = 62;
                                continue;
                            }
                        } else {
                            lean_dec(v_id_3509_);
                            lean_del_object(v___x_3505_);
                            lean_dec(v_n_3500_);
                            return v___x_3510_;
                        }
                    } else {
                        lean_dec(v_a_3508_);
                        lean_del_object(v___x_3505_);
                        lean_dec_ref(v_k_3503_);
                        lean_dec(v_n_3500_);
                        v___x_3522_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__12),
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__12_once),
                            _init_l_Lean_IR_ToIR_lowerCode___closed__12,
                        );
                        v___x_3523_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                            v___x_3522_,
                            v_a_3164_,
                            v_a_3165_,
                            v_a_3166_,
                        );
                        return v___x_3523_;
                    }
                } else {
                    lean_del_object(v___x_3505_);
                    lean_dec_ref(v_k_3503_);
                    lean_dec(v_n_3500_);
                    v_a_3524_ = lean_ctor_get(v___x_3507_, 0);
                    v_isSharedCheck_3531_ = (!lean_is_exclusive(v___x_3507_)) as u8;
                    if v_isSharedCheck_3531_ == 0 {
                        v___x_3526_ = v___x_3507_;
                        v_isShared_3527_ = v_isSharedCheck_3531_;
                        state = 65;
                        continue;
                    } else {
                        lean_inc(v_a_3524_);
                        lean_dec(v___x_3507_);
                        v___x_3526_ = lean_box(0);
                        v_isShared_3527_ = v_isSharedCheck_3531_;
                        state = 65;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_3506_ == 0 {
                    lean_ctor_set_tag(v___x_3505_, 6);
                    lean_ctor_set(v___x_3505_, 2, v_a_3511_);
                    lean_ctor_set(v___x_3505_, 0, v_id_3509_);
                    v___x_3516_ = v___x_3505_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = lean_alloc_ctor(6, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_id_3509_);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_n_3500_);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 2, v_a_3511_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3520_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_check_3501_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3520_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_3502_,
                    );
                    v___x_3516_ = v_reuseFailAlloc_3520_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_3514_ == 0 {
                    lean_ctor_set(v___x_3513_, 0, v___x_3516_);
                    v___x_3518_ = v___x_3513_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
                    v___x_3518_ = v_reuseFailAlloc_3519_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_3518_;
            }
            65 => {
                if v_isShared_3527_ == 0 {
                    v___x_3529_ = v___x_3526_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
                    v___x_3529_ = v_reuseFailAlloc_3530_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_3529_;
            }
            67 => {
                v___x_3546_ = lean_alloc_ctor(7, 3, (2) as u32);
                lean_ctor_set(v___x_3546_, 0, v_id_3540_);
                lean_ctor_set(v___x_3546_, 1, v_n_3534_);
                lean_ctor_set(v___x_3546_, 2, v_a_3542_);
                lean_ctor_set_uint8(
                    v___x_3546_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_check_3535_,
                );
                lean_ctor_set_uint8(
                    v___x_3546_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    v_persistent_3536_,
                );
                if v_isShared_3545_ == 0 {
                    lean_ctor_set(v___x_3544_, 0, v___x_3546_);
                    v___x_3548_ = v___x_3544_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
                    v___x_3548_ = v_reuseFailAlloc_3549_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_3548_;
            }
            69 => {
                if v_isShared_3556_ == 0 {
                    v___x_3558_ = v___x_3555_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
                    v___x_3558_ = v_reuseFailAlloc_3559_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_3558_;
            }
            71 => {
                v___x_3566_ = l_Lean_IR_ToIR_getFVarValue___redArg(v_fvarId_3561_, v_a_3164_);
                lean_dec(v_fvarId_3561_);
                if lean_obj_tag(v___x_3566_) == 0 {
                    v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
                    lean_inc(v_a_3567_);
                    lean_dec_ref_known(v___x_3566_, 1);
                    if lean_obj_tag(v_a_3567_) == 0 {
                        v_id_3568_ = lean_ctor_get(v_a_3567_, 0);
                        lean_inc(v_id_3568_);
                        lean_dec_ref_known(v_a_3567_, 1);
                        v___x_3569_ =
                            l_Lean_IR_ToIR_lowerCode(v_k_3562_, v_a_3164_, v_a_3165_, v_a_3166_);
                        if lean_obj_tag(v___x_3569_) == 0 {
                            v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
                            v_isSharedCheck_3580_ = (!lean_is_exclusive(v___x_3569_)) as u8;
                            if v_isSharedCheck_3580_ == 0 {
                                v___x_3572_ = v___x_3569_;
                                v_isShared_3573_ = v_isSharedCheck_3580_;
                                state = 72;
                                continue;
                            } else {
                                lean_inc(v_a_3570_);
                                lean_dec(v___x_3569_);
                                v___x_3572_ = lean_box(0);
                                v_isShared_3573_ = v_isSharedCheck_3580_;
                                state = 72;
                                continue;
                            }
                        } else {
                            lean_dec(v_id_3568_);
                            lean_del_object(v___x_3564_);
                            return v___x_3569_;
                        }
                    } else {
                        lean_dec(v_a_3567_);
                        lean_del_object(v___x_3564_);
                        lean_dec_ref(v_k_3562_);
                        v___x_3581_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__14),
                            core::ptr::addr_of_mut!(l_Lean_IR_ToIR_lowerCode___closed__14_once),
                            _init_l_Lean_IR_ToIR_lowerCode___closed__14,
                        );
                        v___x_3582_ = l_panic___at___00Lean_IR_ToIR_lowerCode_spec__1(
                            v___x_3581_,
                            v_a_3164_,
                            v_a_3165_,
                            v_a_3166_,
                        );
                        return v___x_3582_;
                    }
                } else {
                    lean_del_object(v___x_3564_);
                    lean_dec_ref(v_k_3562_);
                    v_a_3583_ = lean_ctor_get(v___x_3566_, 0);
                    v_isSharedCheck_3590_ = (!lean_is_exclusive(v___x_3566_)) as u8;
                    if v_isSharedCheck_3590_ == 0 {
                        v___x_3585_ = v___x_3566_;
                        v_isShared_3586_ = v_isSharedCheck_3590_;
                        state = 75;
                        continue;
                    } else {
                        lean_inc(v_a_3583_);
                        lean_dec(v___x_3566_);
                        v___x_3585_ = lean_box(0);
                        v_isShared_3586_ = v_isSharedCheck_3590_;
                        state = 75;
                        continue;
                    }
                }
            }
            72 => {
                if v_isShared_3565_ == 0 {
                    lean_ctor_set_tag(v___x_3564_, 8);
                    lean_ctor_set(v___x_3564_, 1, v_a_3570_);
                    lean_ctor_set(v___x_3564_, 0, v_id_3568_);
                    v___x_3575_ = v___x_3564_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_id_3568_);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 1, v_a_3570_);
                    v___x_3575_ = v_reuseFailAlloc_3579_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                if v_isShared_3573_ == 0 {
                    lean_ctor_set(v___x_3572_, 0, v___x_3575_);
                    v___x_3577_ = v___x_3572_;
                    state = 74;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
                    v___x_3577_ = v_reuseFailAlloc_3578_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                return v___x_3577_;
            }
            75 => {
                if v_isShared_3586_ == 0 {
                    v___x_3588_ = v___x_3585_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
                    v___x_3588_ = v_reuseFailAlloc_3589_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_3588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(
    mut v_decl_3592_: *mut LeanObject,
    mut v_k_3593_: *mut LeanObject,
    mut v_a_3594_: *mut LeanObject,
    mut v_a_3595_: *mut LeanObject,
    mut v_a_3596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_3598_ = lean_ctor_get(v_decl_3592_, 0);
                lean_inc(v_fvarId_3598_);
                lean_dec_ref(v_decl_3592_);
                v___x_3599_ = l_Lean_IR_ToIR_bindErased___redArg(v_fvarId_3598_, v_a_3594_);
                if lean_obj_tag(v___x_3599_) == 0 {
                    lean_dec_ref_known(v___x_3599_, 1);
                    v___x_3600_ =
                        l_Lean_IR_ToIR_lowerCode(v_k_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
                    return v___x_3600_;
                } else {
                    lean_dec_ref(v_k_3593_);
                    v_a_3601_ = lean_ctor_get(v___x_3599_, 0);
                    v_isSharedCheck_3608_ = (!lean_is_exclusive(v___x_3599_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v___x_3603_ = v___x_3599_;
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3601_);
                        lean_dec(v___x_3599_);
                        v___x_3603_ = lean_box(0);
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3604_ == 0 {
                    v___x_3606_ = v___x_3603_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(
    mut v_decl_3609_: *mut LeanObject,
    mut v_k_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
    mut v_a_3612_: *mut LeanObject,
    mut v_a_3613_: *mut LeanObject,
    mut v_a_3614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3615_: *mut LeanObject = core::ptr::null_mut();
    v_res_3615_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(
        v_decl_3609_,
        v_k_3610_,
        v_a_3611_,
        v_a_3612_,
        v_a_3613_,
    );
    lean_dec(v_a_3613_);
    lean_dec_ref(v_a_3612_);
    lean_dec(v_a_3611_);
    return v_res_3615_;
}
pub unsafe fn l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue___boxed(
    mut v_decl_3616_: *mut LeanObject,
    mut v_k_3617_: *mut LeanObject,
    mut v_fvarId_3618_: *mut LeanObject,
    mut v_f_3619_: *mut LeanObject,
    mut v_a_3620_: *mut LeanObject,
    mut v_a_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
    mut v_a_3623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3624_: *mut LeanObject = core::ptr::null_mut();
    v_res_3624_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_withGetFVarValue(
        v_decl_3616_,
        v_k_3617_,
        v_fvarId_3618_,
        v_f_3619_,
        v_a_3620_,
        v_a_3621_,
        v_a_3622_,
    );
    lean_dec(v_a_3622_);
    lean_dec_ref(v_a_3621_);
    lean_dec(v_a_3620_);
    lean_dec(v_fvarId_3618_);
    return v_res_3624_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(
    mut v_sz_3625_: *mut LeanObject,
    mut v_i_3626_: *mut LeanObject,
    mut v_bs_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
    mut v___y_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
    mut v___y_3631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3632_: usize = 0;
    let mut v_i_boxed_3633_: usize = 0;
    let mut v_res_3634_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3632_ = lean_unbox_usize(v_sz_3625_);
    lean_dec(v_sz_3625_);
    v_i_boxed_3633_ = lean_unbox_usize(v_i_3626_);
    lean_dec(v_i_3626_);
    v_res_3634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__4(v_sz_boxed_3632_, v_i_boxed_3633_, v_bs_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
    lean_dec(v___y_3630_);
    lean_dec_ref(v___y_3629_);
    lean_dec(v___y_3628_);
    return v_res_3634_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerAlt___boxed(
    mut v_a_3635_: *mut LeanObject,
    mut v_a_3636_: *mut LeanObject,
    mut v_a_3637_: *mut LeanObject,
    mut v_a_3638_: *mut LeanObject,
    mut v_a_3639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3640_: *mut LeanObject = core::ptr::null_mut();
    v_res_3640_ = l_Lean_IR_ToIR_lowerAlt(v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_);
    lean_dec(v_a_3638_);
    lean_dec_ref(v_a_3637_);
    lean_dec(v_a_3636_);
    return v_res_3640_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerLet___boxed(
    mut v_decl_3641_: *mut LeanObject,
    mut v_k_3642_: *mut LeanObject,
    mut v_a_3643_: *mut LeanObject,
    mut v_a_3644_: *mut LeanObject,
    mut v_a_3645_: *mut LeanObject,
    mut v_a_3646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3647_: *mut LeanObject = core::ptr::null_mut();
    v_res_3647_ = l_Lean_IR_ToIR_lowerLet(v_decl_3641_, v_k_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
    lean_dec(v_a_3645_);
    lean_dec_ref(v_a_3644_);
    lean_dec(v_a_3643_);
    return v_res_3647_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerCode___boxed(
    mut v_c_3648_: *mut LeanObject,
    mut v_a_3649_: *mut LeanObject,
    mut v_a_3650_: *mut LeanObject,
    mut v_a_3651_: *mut LeanObject,
    mut v_a_3652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3653_: *mut LeanObject = core::ptr::null_mut();
    v_res_3653_ = l_Lean_IR_ToIR_lowerCode(v_c_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
    lean_dec(v_a_3651_);
    lean_dec_ref(v_a_3650_);
    lean_dec(v_a_3649_);
    return v_res_3653_;
}
pub unsafe fn l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(
    mut v_decl_3654_: *mut LeanObject,
    mut v_k_3655_: *mut LeanObject,
    mut v_x_3656_: *mut LeanObject,
    mut v_a_3657_: *mut LeanObject,
    mut v_a_3658_: *mut LeanObject,
    mut v_a_3659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    v___x_3661_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(
        v_decl_3654_,
        v_k_3655_,
        v_a_3657_,
        v_a_3658_,
        v_a_3659_,
    );
    return v___x_3661_;
}
pub unsafe fn l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(
    mut v_decl_3662_: *mut LeanObject,
    mut v_k_3663_: *mut LeanObject,
    mut v_x_3664_: *mut LeanObject,
    mut v_a_3665_: *mut LeanObject,
    mut v_a_3666_: *mut LeanObject,
    mut v_a_3667_: *mut LeanObject,
    mut v_a_3668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3669_: *mut LeanObject = core::ptr::null_mut();
    v_res_3669_ = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(
        v_decl_3662_,
        v_k_3663_,
        v_x_3664_,
        v_a_3665_,
        v_a_3666_,
        v_a_3667_,
    );
    lean_dec(v_a_3667_);
    lean_dec_ref(v_a_3666_);
    lean_dec(v_a_3665_);
    return v_res_3669_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(
    mut v_sz_3670_: usize,
    mut v_i_3671_: usize,
    mut v_bs_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
    mut v___y_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    v___x_3677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_3670_, v_i_3671_, v_bs_3672_, v___y_3673_);
    return v___x_3677_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(
    mut v_sz_3678_: *mut LeanObject,
    mut v_i_3679_: *mut LeanObject,
    mut v_bs_3680_: *mut LeanObject,
    mut v___y_3681_: *mut LeanObject,
    mut v___y_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3685_: usize = 0;
    let mut v_i_boxed_3686_: usize = 0;
    let mut v_res_3687_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3685_ = lean_unbox_usize(v_sz_3678_);
    lean_dec(v_sz_3678_);
    v_i_boxed_3686_ = lean_unbox_usize(v_i_3679_);
    lean_dec(v_i_3679_);
    v_res_3687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(v_sz_boxed_3685_, v_i_boxed_3686_, v_bs_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
    lean_dec(v___y_3683_);
    lean_dec_ref(v___y_3682_);
    lean_dec(v___y_3681_);
    return v_res_3687_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(
    mut v_sz_3688_: usize,
    mut v_i_3689_: usize,
    mut v_bs_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(v_sz_3688_, v_i_3689_, v_bs_3690_, v___y_3691_);
    return v___x_3695_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(
    mut v_sz_3696_: *mut LeanObject,
    mut v_i_3697_: *mut LeanObject,
    mut v_bs_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
    mut v___y_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3703_: usize = 0;
    let mut v_i_boxed_3704_: usize = 0;
    let mut v_res_3705_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3703_ = lean_unbox_usize(v_sz_3696_);
    lean_dec(v_sz_3696_);
    v_i_boxed_3704_ = lean_unbox_usize(v_i_3697_);
    lean_dec(v_i_3697_);
    v_res_3705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(v_sz_boxed_3703_, v_i_boxed_3704_, v_bs_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
    lean_dec(v___y_3701_);
    lean_dec_ref(v___y_3700_);
    lean_dec(v___y_3699_);
    return v_res_3705_;
}
pub unsafe fn l_Lean_IR_ToIR_lowerDecl(
    mut v_d_3706_: *mut LeanObject,
    mut v_a_3707_: *mut LeanObject,
    mut v_a_3708_: *mut LeanObject,
    mut v_a_3709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3716_: usize = 0;
    let mut v___x_3717_: usize = 0;
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3722_: u8 = 0;
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3727_: u8 = 0;
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut v_a_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v_isSharedCheck_3750_: u8 = 0;
    let mut v_externAttrData_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3754_: u8 = 0;
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3767_: u8 = 0;
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3772_: u8 = 0;
    let mut v_unused_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3774_: u8 = 0;
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut v_a_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_3711_ = lean_ctor_get(v_d_3706_, 0);
                lean_inc_ref(v_toSignature_3711_);
                v_value_3712_ = lean_ctor_get(v_d_3706_, 1);
                lean_inc_ref(v_value_3712_);
                lean_dec_ref(v_d_3706_);
                v_name_3713_ = lean_ctor_get(v_toSignature_3711_, 0);
                lean_inc(v_name_3713_);
                v_type_3714_ = lean_ctor_get(v_toSignature_3711_, 2);
                lean_inc_ref(v_type_3714_);
                v_params_3715_ = lean_ctor_get(v_toSignature_3711_, 3);
                lean_inc_ref(v_params_3715_);
                lean_dec_ref(v_toSignature_3711_);
                v_sz_3716_ = lean_array_size(v_params_3715_);
                v___x_3717_ = 0usize;
                v___x_3718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___redArg(v_sz_3716_, v___x_3717_, v_params_3715_, v_a_3707_);
                if lean_obj_tag(v___x_3718_) == 0 {
                    v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
                    v_isSharedCheck_3775_ = (!lean_is_exclusive(v___x_3718_)) as u8;
                    if v_isSharedCheck_3775_ == 0 {
                        v___x_3721_ = v___x_3718_;
                        v_isShared_3722_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3719_);
                        lean_dec(v___x_3718_);
                        v___x_3721_ = lean_box(0);
                        v_isShared_3722_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_3714_);
                    lean_dec(v_name_3713_);
                    lean_dec_ref(v_value_3712_);
                    v_a_3776_ = lean_ctor_get(v___x_3718_, 0);
                    v_isSharedCheck_3783_ = (!lean_is_exclusive(v___x_3718_)) as u8;
                    if v_isSharedCheck_3783_ == 0 {
                        v___x_3778_ = v___x_3718_;
                        v_isShared_3779_ = v_isSharedCheck_3783_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3776_);
                        lean_dec(v___x_3718_);
                        v___x_3778_ = lean_box(0);
                        v_isShared_3779_ = v_isSharedCheck_3783_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3723_ = l_Lean_IR_toIRType(v_type_3714_);
                lean_dec_ref(v_type_3714_);
                if lean_obj_tag(v_value_3712_) == 0 {
                    lean_del_object(v___x_3721_);
                    v_code_3724_ = lean_ctor_get(v_value_3712_, 0);
                    v_isSharedCheck_3750_ = (!lean_is_exclusive(v_value_3712_)) as u8;
                    if v_isSharedCheck_3750_ == 0 {
                        v___x_3726_ = v_value_3712_;
                        v_isShared_3727_ = v_isSharedCheck_3750_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_code_3724_);
                        lean_dec(v_value_3712_);
                        v___x_3726_ = lean_box(0);
                        v_isShared_3727_ = v_isSharedCheck_3750_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_externAttrData_3751_ = lean_ctor_get(v_value_3712_, 0);
                    v_isSharedCheck_3774_ = (!lean_is_exclusive(v_value_3712_)) as u8;
                    if v_isSharedCheck_3774_ == 0 {
                        v___x_3753_ = v_value_3712_;
                        v_isShared_3754_ = v_isSharedCheck_3774_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_externAttrData_3751_);
                        lean_dec(v_value_3712_);
                        v___x_3753_ = lean_box(0);
                        v_isShared_3754_ = v_isSharedCheck_3774_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3728_ =
                    l_Lean_IR_ToIR_lowerCode(v_code_3724_, v_a_3707_, v_a_3708_, v_a_3709_);
                if lean_obj_tag(v___x_3728_) == 0 {
                    v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
                    v_isSharedCheck_3741_ = (!lean_is_exclusive(v___x_3728_)) as u8;
                    if v_isSharedCheck_3741_ == 0 {
                        v___x_3731_ = v___x_3728_;
                        v_isShared_3732_ = v_isSharedCheck_3741_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3729_);
                        lean_dec(v___x_3728_);
                        v___x_3731_ = lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3741_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3726_);
                    lean_dec(v___x_3723_);
                    lean_dec(v_a_3719_);
                    lean_dec(v_name_3713_);
                    v_a_3742_ = lean_ctor_get(v___x_3728_, 0);
                    v_isSharedCheck_3749_ = (!lean_is_exclusive(v___x_3728_)) as u8;
                    if v_isSharedCheck_3749_ == 0 {
                        v___x_3744_ = v___x_3728_;
                        v_isShared_3745_ = v_isSharedCheck_3749_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3742_);
                        lean_dec(v___x_3728_);
                        v___x_3744_ = lean_box(0);
                        v_isShared_3745_ = v_isSharedCheck_3749_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3733_ = lean_box(0);
                v___x_3734_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3734_, 0, v_name_3713_);
                lean_ctor_set(v___x_3734_, 1, v_a_3719_);
                lean_ctor_set(v___x_3734_, 2, v___x_3723_);
                lean_ctor_set(v___x_3734_, 3, v_a_3729_);
                lean_ctor_set(v___x_3734_, 4, v___x_3733_);
                if v_isShared_3727_ == 0 {
                    lean_ctor_set_tag(v___x_3726_, 1);
                    lean_ctor_set(v___x_3726_, 0, v___x_3734_);
                    v___x_3736_ = v___x_3726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3734_);
                    v___x_3736_ = v_reuseFailAlloc_3740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3732_ == 0 {
                    lean_ctor_set(v___x_3731_, 0, v___x_3736_);
                    v___x_3738_ = v___x_3731_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
                    v___x_3738_ = v_reuseFailAlloc_3739_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3738_;
            }
            6 => {
                if v_isShared_3745_ == 0 {
                    v___x_3747_ = v___x_3744_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
                    v___x_3747_ = v_reuseFailAlloc_3748_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3747_;
            }
            8 => {
                v___x_3755_ = l_List_isEmpty___redArg(v_externAttrData_3751_);
                if v___x_3755_ == 0 {
                    v___x_3756_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v___x_3756_, 0, v_name_3713_);
                    lean_ctor_set(v___x_3756_, 1, v_a_3719_);
                    lean_ctor_set(v___x_3756_, 2, v___x_3723_);
                    lean_ctor_set(v___x_3756_, 3, v_externAttrData_3751_);
                    if v_isShared_3754_ == 0 {
                        lean_ctor_set(v___x_3753_, 0, v___x_3756_);
                        v___x_3758_ = v___x_3753_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3756_);
                        v___x_3758_ = v_reuseFailAlloc_3762_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3753_);
                    lean_dec(v_externAttrData_3751_);
                    lean_del_object(v___x_3721_);
                    v___x_3763_ = l_Lean_IR_mkDummyExternDecl(v_name_3713_, v_a_3719_, v___x_3723_);
                    v___x_3764_ = l_Lean_IR_ToIR_addDecl___redArg(v___x_3763_, v_a_3709_);
                    v_isSharedCheck_3772_ = (!lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3772_ == 0 {
                        v_unused_3773_ = lean_ctor_get(v___x_3764_, 0);
                        lean_dec(v_unused_3773_);
                        v___x_3766_ = v___x_3764_;
                        v_isShared_3767_ = v_isSharedCheck_3772_;
                        state = 11;
                        continue;
                    } else {
                        lean_dec(v___x_3764_);
                        v___x_3766_ = lean_box(0);
                        v_isShared_3767_ = v_isSharedCheck_3772_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3722_ == 0 {
                    lean_ctor_set(v___x_3721_, 0, v___x_3758_);
                    v___x_3760_ = v___x_3721_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3758_);
                    v___x_3760_ = v_reuseFailAlloc_3761_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3760_;
            }
            11 => {
                v___x_3768_ = lean_box(0);
                if v_isShared_3767_ == 0 {
                    lean_ctor_set(v___x_3766_, 0, v___x_3768_);
                    v___x_3770_ = v___x_3766_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
                    v___x_3770_ = v_reuseFailAlloc_3771_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3770_;
            }
            13 => {
                if v_isShared_3779_ == 0 {
                    v___x_3781_ = v___x_3778_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
                    v___x_3781_ = v_reuseFailAlloc_3782_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_ToIR_lowerDecl___boxed(
    mut v_d_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
    mut v_a_3786_: *mut LeanObject,
    mut v_a_3787_: *mut LeanObject,
    mut v_a_3788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3789_: *mut LeanObject = core::ptr::null_mut();
    v_res_3789_ = l_Lean_IR_ToIR_lowerDecl(v_d_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
    lean_dec(v_a_3787_);
    lean_dec_ref(v_a_3786_);
    lean_dec(v_a_3785_);
    return v_res_3789_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(
    mut v_as_3790_: *mut LeanObject,
    mut v_sz_3791_: usize,
    mut v_i_3792_: usize,
    mut v_b_3793_: *mut LeanObject,
    mut v___y_3794_: *mut LeanObject,
    mut v___y_3795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: usize = 0;
    let mut v___x_3806_: usize = 0;
    let mut v_val_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3813_: u8 = 0;
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3797_ = lean_usize_dec_lt(v_i_3792_, v_sz_3791_);
                if v___x_3797_ == 0 {
                    v___x_3798_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3798_, 0, v_b_3793_);
                    return v___x_3798_;
                } else {
                    v_a_3799_ = lean_array_uget_borrowed(v_as_3790_, v_i_3792_);
                    lean_inc(v_a_3799_);
                    v___x_3800_ = lean_alloc_closure(
                        l_Lean_IR_ToIR_lowerDecl___boxed as *mut core::ffi::c_void,
                        5,
                        1,
                    );
                    lean_closure_set(v___x_3800_, 0, v_a_3799_);
                    v___x_3801_ =
                        l_Lean_IR_ToIR_M_run___redArg(v___x_3800_, v___y_3794_, v___y_3795_);
                    if lean_obj_tag(v___x_3801_) == 0 {
                        v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
                        lean_inc(v_a_3802_);
                        lean_dec_ref_known(v___x_3801_, 1);
                        if lean_obj_tag(v_a_3802_) == 1 {
                            v_val_3808_ = lean_ctor_get(v_a_3802_, 0);
                            lean_inc(v_val_3808_);
                            lean_dec_ref_known(v_a_3802_, 1);
                            v___x_3809_ = lean_array_push(v_b_3793_, v_val_3808_);
                            v_a_3804_ = v___x_3809_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3802_);
                            v_a_3804_ = v_b_3793_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_3793_);
                        v_a_3810_ = lean_ctor_get(v___x_3801_, 0);
                        v_isSharedCheck_3817_ = (!lean_is_exclusive(v___x_3801_)) as u8;
                        if v_isSharedCheck_3817_ == 0 {
                            v___x_3812_ = v___x_3801_;
                            v_isShared_3813_ = v_isSharedCheck_3817_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3810_);
                            lean_dec(v___x_3801_);
                            v___x_3812_ = lean_box(0);
                            v_isShared_3813_ = v_isSharedCheck_3817_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3805_ = 1usize;
                v___x_3806_ = lean_usize_add(v_i_3792_, v___x_3805_);
                v_i_3792_ = v___x_3806_;
                v_b_3793_ = v_a_3804_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3813_ == 0 {
                    v___x_3815_ = v___x_3812_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
                    v___x_3815_ = v_reuseFailAlloc_3816_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(
    mut v_as_3818_: *mut LeanObject,
    mut v_sz_3819_: *mut LeanObject,
    mut v_i_3820_: *mut LeanObject,
    mut v_b_3821_: *mut LeanObject,
    mut v___y_3822_: *mut LeanObject,
    mut v___y_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3825_: usize = 0;
    let mut v_i_boxed_3826_: usize = 0;
    let mut v_res_3827_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3825_ = lean_unbox_usize(v_sz_3819_);
    lean_dec(v_sz_3819_);
    v_i_boxed_3826_ = lean_unbox_usize(v_i_3820_);
    lean_dec(v_i_3820_);
    v_res_3827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_as_3818_, v_sz_boxed_3825_, v_i_boxed_3826_, v_b_3821_, v___y_3822_, v___y_3823_);
    lean_dec(v___y_3823_);
    lean_dec_ref(v___y_3822_);
    lean_dec_ref(v_as_3818_);
    return v_res_3827_;
}
pub unsafe fn l_Lean_IR_toIR(
    mut v_decls_3830_: *mut LeanObject,
    mut v_a_3831_: *mut LeanObject,
    mut v_a_3832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_irDecls_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3835_: usize = 0;
    let mut v___x_3836_: usize = 0;
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    v_irDecls_3834_ = l_Lean_IR_toIR___closed__0;
    v_sz_3835_ = lean_array_size(v_decls_3830_);
    v___x_3836_ = 0usize;
    v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(v_decls_3830_, v_sz_3835_, v___x_3836_, v_irDecls_3834_, v_a_3831_, v_a_3832_);
    return v___x_3837_;
}
pub unsafe fn l_Lean_IR_toIR___boxed(
    mut v_decls_3838_: *mut LeanObject,
    mut v_a_3839_: *mut LeanObject,
    mut v_a_3840_: *mut LeanObject,
    mut v_a_3841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3842_: *mut LeanObject = core::ptr::null_mut();
    v_res_3842_ = l_Lean_IR_toIR(v_decls_3838_, v_a_3839_, v_a_3840_);
    lean_dec(v_a_3840_);
    lean_dec_ref(v_a_3839_);
    lean_dec_ref(v_decls_3838_);
    return v_res_3842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_ToIR(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_ToIRType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_ToIR(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_ToIR(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_ToIRType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_ToIR(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_ToIR(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_ToIR(builtin);
}
