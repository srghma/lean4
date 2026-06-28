// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceArity
// Imports: Lean.Compiler.LCNF.Internalize
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Param_toArg___redArg, l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg, l_Lean_Compiler_LCNF_eraseParams___redArg,
    l_Lean_Compiler_LCNF_getPurity___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    l_Lean_Compiler_LCNF_Code_inferType, l_Lean_Compiler_LCNF_mkAuxLetDecl,
    l_Lean_Compiler_LCNF_mkForallParams,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize, l_Lean_Compiler_LCNF_Internalize_internalizeParam,
    runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::l_Lean_Compiler_LCNF_Decl_saveMono___redArg;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_FVarIdSet_insert, l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_7, lean_apply_8, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_FindUsed_visit___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value)
        as *mut LeanObject;
static mut l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value: LeanStringObject<34> =
    LeanStringObject {
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value: LeanStringObject<68> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105,
            108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97,
            110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 117, 112, 100,
            97, 116, 101, 70, 117, 110, 73, 109, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            66, 97, 115, 105, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value: LeanStringObject<3> =
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
        m_data: [95, 120, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value)
                as *mut LeanObject,
            7699194985028780469 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [95, 114, 101, 100, 65, 114, 103, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value)
                as *mut LeanObject,
            13427258015795454894 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value: LeanStringObject<9> =
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
        m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value: LeanStringObject<12> =
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
        m_data: [114, 101, 100, 117, 99, 101, 65, 114, 105, 116, 121, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value) as *mut LeanObject;
static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value)
                as *mut LeanObject,
            2042452093243897853 as *mut LeanObject,
        ],
    };
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value)
                as *mut LeanObject,
            17070998189071160153 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value: LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value: LeanStringObject<16> =
    LeanStringObject {
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
            44, 32, 117, 115, 101, 100, 32, 112, 97, 114, 97, 109, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_reduceArity___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_LCNF_reduceArity___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_reduceArity___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value)
            as *mut LeanObject,
        6230351632210813039 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_reduceArity___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_reduceArity___closed__2_value: LeanCtorObject<4> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__0_value) as *mut LeanObject,
        257 as *mut LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_reduceArity___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_reduceArity: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [82, 101, 100, 117, 99, 101, 65, 114, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,13109072740202689192 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,4920082522366582657 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,14590473376816633124 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value) as *mut LeanObject,4817029385054651662 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,4895640151090576375 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,855462560601428038 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,8803284079650313463 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,13950663889180613002 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value) as *mut LeanObject,3409869455520383320 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,75999622856309905 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject,18075986562369520856 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(
    mut v_a_2150_: *mut LeanObject,
    mut v_x_2151_: *mut LeanObject,
) -> u8 {
    let mut v___x_2152_: u8 = 0;
    let mut v_key_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2151_) == 0 {
                    v___x_2152_ = 0;
                    return v___x_2152_;
                } else {
                    v_key_2153_ = lean_ctor_get(v_x_2151_, 0);
                    v_tail_2154_ = lean_ctor_get(v_x_2151_, 2);
                    v___x_2155_ = l_Lean_instBEqFVarId_beq(v_key_2153_, v_a_2150_);
                    if v___x_2155_ == 0 {
                        v_x_2151_ = v_tail_2154_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2155_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(
    mut v_a_2157_: *mut LeanObject,
    mut v_x_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2159_: u8 = 0;
    let mut v_r_2160_: *mut LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_2157_, v_x_2158_);
    lean_dec(v_x_2158_);
    lean_dec(v_a_2157_);
    v_r_2160_ = lean_box((v_res_2159_) as usize);
    return v_r_2160_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2161_: *mut LeanObject,
    mut v_x_2162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: u64 = 0;
    let mut v___x_2171_: u64 = 0;
    let mut v___x_2172_: u64 = 0;
    let mut v_fold_2173_: u64 = 0;
    let mut v___x_2174_: u64 = 0;
    let mut v___x_2175_: u64 = 0;
    let mut v___x_2176_: u64 = 0;
    let mut v___x_2177_: usize = 0;
    let mut v___x_2178_: usize = 0;
    let mut v___x_2179_: usize = 0;
    let mut v___x_2180_: usize = 0;
    let mut v___x_2181_: usize = 0;
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2162_) == 0 {
                    return v_x_2161_;
                } else {
                    v_key_2163_ = lean_ctor_get(v_x_2162_, 0);
                    v_value_2164_ = lean_ctor_get(v_x_2162_, 1);
                    v_tail_2165_ = lean_ctor_get(v_x_2162_, 2);
                    v_isSharedCheck_2188_ = (!lean_is_exclusive(v_x_2162_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2167_ = v_x_2162_;
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2165_);
                        lean_inc(v_value_2164_);
                        lean_inc(v_key_2163_);
                        lean_dec(v_x_2162_);
                        v___x_2167_ = lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2169_ = lean_array_get_size(v_x_2161_);
                v___x_2170_ = l_Lean_instHashableFVarId_hash(v_key_2163_);
                v___x_2171_ = 32u64;
                v___x_2172_ = lean_uint64_shift_right(v___x_2170_, v___x_2171_);
                v_fold_2173_ = lean_uint64_xor(v___x_2170_, v___x_2172_);
                v___x_2174_ = 16u64;
                v___x_2175_ = lean_uint64_shift_right(v_fold_2173_, v___x_2174_);
                v___x_2176_ = lean_uint64_xor(v_fold_2173_, v___x_2175_);
                v___x_2177_ = lean_uint64_to_usize(v___x_2176_);
                v___x_2178_ = lean_usize_of_nat(v___x_2169_);
                v___x_2179_ = 1usize;
                v___x_2180_ = lean_usize_sub(v___x_2178_, v___x_2179_);
                v___x_2181_ = lean_usize_land(v___x_2177_, v___x_2180_);
                v___x_2182_ = lean_array_uget_borrowed(v_x_2161_, v___x_2181_);
                lean_inc(v___x_2182_);
                if v_isShared_2168_ == 0 {
                    lean_ctor_set(v___x_2167_, 2, v___x_2182_);
                    v___x_2184_ = v___x_2167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_key_2163_);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_value_2164_);
                    lean_ctor_set(v_reuseFailAlloc_2187_, 2, v___x_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2185_ = lean_array_uset(v_x_2161_, v___x_2181_, v___x_2184_);
                v_x_2161_ = v___x_2185_;
                v_x_2162_ = v_tail_2165_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(
    mut v_i_2189_: *mut LeanObject,
    mut v_source_2190_: *mut LeanObject,
    mut v_target_2191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v_es_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2192_ = lean_array_get_size(v_source_2190_);
                v___x_2193_ = lean_nat_dec_lt(v_i_2189_, v___x_2192_);
                if v___x_2193_ == 0 {
                    lean_dec_ref(v_source_2190_);
                    lean_dec(v_i_2189_);
                    return v_target_2191_;
                } else {
                    v_es_2194_ = lean_array_fget(v_source_2190_, v_i_2189_);
                    v___x_2195_ = lean_box(0);
                    v_source_2196_ = lean_array_fset(v_source_2190_, v_i_2189_, v___x_2195_);
                    v_target_2197_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2191_, v_es_2194_);
                    v___x_2198_ = lean_unsigned_to_nat(1);
                    v___x_2199_ = lean_nat_add(v_i_2189_, v___x_2198_);
                    lean_dec(v_i_2189_);
                    v_i_2189_ = v___x_2199_;
                    v_source_2190_ = v_source_2196_;
                    v_target_2191_ = v_target_2197_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(
    mut v_data_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    v___x_2202_ = lean_array_get_size(v_data_2201_);
    v___x_2203_ = lean_unsigned_to_nat(2);
    v_nbuckets_2204_ = lean_nat_mul(v___x_2202_, v___x_2203_);
    v___x_2205_ = lean_unsigned_to_nat(0);
    v___x_2206_ = lean_box(0);
    v___x_2207_ = lean_mk_array(v_nbuckets_2204_, v___x_2206_);
    v___x_2208_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v___x_2205_, v_data_2201_, v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(
    mut v_m_2209_: *mut LeanObject,
    mut v_a_2210_: *mut LeanObject,
    mut v_b_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u64 = 0;
    let mut v___x_2216_: u64 = 0;
    let mut v___x_2217_: u64 = 0;
    let mut v_fold_2218_: u64 = 0;
    let mut v___x_2219_: u64 = 0;
    let mut v___x_2220_: u64 = 0;
    let mut v___x_2221_: u64 = 0;
    let mut v___x_2222_: usize = 0;
    let mut v___x_2223_: usize = 0;
    let mut v___x_2224_: usize = 0;
    let mut v___x_2225_: usize = 0;
    let mut v___x_2226_: usize = 0;
    let mut v_bkt_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v_val_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_unused_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2212_ = lean_ctor_get(v_m_2209_, 0);
                v_buckets_2213_ = lean_ctor_get(v_m_2209_, 1);
                v___x_2214_ = lean_array_get_size(v_buckets_2213_);
                v___x_2215_ = l_Lean_instHashableFVarId_hash(v_a_2210_);
                v___x_2216_ = 32u64;
                v___x_2217_ = lean_uint64_shift_right(v___x_2215_, v___x_2216_);
                v_fold_2218_ = lean_uint64_xor(v___x_2215_, v___x_2217_);
                v___x_2219_ = 16u64;
                v___x_2220_ = lean_uint64_shift_right(v_fold_2218_, v___x_2219_);
                v___x_2221_ = lean_uint64_xor(v_fold_2218_, v___x_2220_);
                v___x_2222_ = lean_uint64_to_usize(v___x_2221_);
                v___x_2223_ = lean_usize_of_nat(v___x_2214_);
                v___x_2224_ = 1usize;
                v___x_2225_ = lean_usize_sub(v___x_2223_, v___x_2224_);
                v___x_2226_ = lean_usize_land(v___x_2222_, v___x_2225_);
                v_bkt_2227_ = lean_array_uget_borrowed(v_buckets_2213_, v___x_2226_);
                v___x_2228_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_2210_, v_bkt_2227_);
                if v___x_2228_ == 0 {
                    lean_inc_ref(v_buckets_2213_);
                    lean_inc(v_size_2212_);
                    v_isSharedCheck_2249_ = (!lean_is_exclusive(v_m_2209_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v_unused_2250_ = lean_ctor_get(v_m_2209_, 1);
                        lean_dec(v_unused_2250_);
                        v_unused_2251_ = lean_ctor_get(v_m_2209_, 0);
                        lean_dec(v_unused_2251_);
                        v___x_2230_ = v_m_2209_;
                        v_isShared_2231_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_2209_);
                        v___x_2230_ = lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2211_);
                    lean_dec(v_a_2210_);
                    return v_m_2209_;
                }
            }
            1 => {
                v___x_2232_ = lean_unsigned_to_nat(1);
                v_size_x27_2233_ = lean_nat_add(v_size_2212_, v___x_2232_);
                lean_dec(v_size_2212_);
                lean_inc(v_bkt_2227_);
                v___x_2234_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2234_, 0, v_a_2210_);
                lean_ctor_set(v___x_2234_, 1, v_b_2211_);
                lean_ctor_set(v___x_2234_, 2, v_bkt_2227_);
                v_buckets_x27_2235_ = lean_array_uset(v_buckets_2213_, v___x_2226_, v___x_2234_);
                v___x_2236_ = lean_unsigned_to_nat(4);
                v___x_2237_ = lean_nat_mul(v_size_x27_2233_, v___x_2236_);
                v___x_2238_ = lean_unsigned_to_nat(3);
                v___x_2239_ = lean_nat_div(v___x_2237_, v___x_2238_);
                lean_dec(v___x_2237_);
                v___x_2240_ = lean_array_get_size(v_buckets_x27_2235_);
                v___x_2241_ = lean_nat_dec_le(v___x_2239_, v___x_2240_);
                lean_dec(v___x_2239_);
                if v___x_2241_ == 0 {
                    v_val_2242_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_buckets_x27_2235_);
                    if v_isShared_2231_ == 0 {
                        lean_ctor_set(v___x_2230_, 1, v_val_2242_);
                        lean_ctor_set(v___x_2230_, 0, v_size_x27_2233_);
                        v___x_2244_ = v___x_2230_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_size_x27_2233_);
                        lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_val_2242_);
                        v___x_2244_ = v_reuseFailAlloc_2245_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2231_ == 0 {
                        lean_ctor_set(v___x_2230_, 1, v_buckets_x27_2235_);
                        lean_ctor_set(v___x_2230_, 0, v_size_x27_2233_);
                        v___x_2247_ = v___x_2230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_size_x27_2233_);
                        lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_buckets_x27_2235_);
                        v___x_2247_ = v_reuseFailAlloc_2248_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2244_;
            }
            3 => {
                return v___x_2247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(
    mut v_k_2252_: *mut LeanObject,
    mut v_t_2253_: *mut LeanObject,
) -> u8 {
    let mut v_k_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: u8 = 0;
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2253_) == 0 {
                    v_k_2254_ = lean_ctor_get(v_t_2253_, 1);
                    v_l_2255_ = lean_ctor_get(v_t_2253_, 3);
                    v_r_2256_ = lean_ctor_get(v_t_2253_, 4);
                    v___x_2257_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2252_, v_k_2254_);
                    match v___x_2257_ {
                        0 => {
                            v_t_2253_ = v_l_2255_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2259_ = 1;
                            return v___x_2259_;
                        }
                        _ => {
                            v_t_2253_ = v_r_2256_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2261_ = 0;
                    return v___x_2261_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(
    mut v_k_2262_: *mut LeanObject,
    mut v_t_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2264_: u8 = 0;
    let mut v_r_2265_: *mut LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_2262_, v_t_2263_);
    lean_dec(v_t_2263_);
    lean_dec(v_k_2262_);
    v_r_2265_ = lean_box((v_res_2264_) as usize);
    return v_r_2265_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
    mut v_fvarId_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    v_params_2270_ = lean_ctor_get(v_a_2267_, 1);
    v___x_2271_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_fvarId_2266_, v_params_2270_);
    if v___x_2271_ == 0 {
        let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fvarId_2266_);
        v___x_2272_ = lean_box(0);
        v___x_2273_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2273_, 0, v___x_2272_);
        return v___x_2273_;
    } else {
        let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
        v___x_2274_ = lean_st_ref_take(v_a_2268_);
        v___x_2275_ = lean_box(0);
        v___x_2276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___x_2274_, v_fvarId_2266_, v___x_2275_);
        v___x_2277_ = lean_st_ref_set(v_a_2268_, v___x_2276_);
        v___x_2278_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2278_, 0, v___x_2275_);
        return v___x_2278_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(
    mut v_fvarId_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2283_: *mut LeanObject = core::ptr::null_mut();
    v_res_2283_ =
        l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_2279_, v_a_2280_, v_a_2281_);
    lean_dec(v_a_2281_);
    lean_dec_ref(v_a_2280_);
    return v_res_2283_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar(
    mut v_fvarId_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
    mut v_a_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    v___x_2292_ =
        l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_2284_, v_a_2285_, v_a_2286_);
    return v___x_2292_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(
    mut v_fvarId_2293_: *mut LeanObject,
    mut v_a_2294_: *mut LeanObject,
    mut v_a_2295_: *mut LeanObject,
    mut v_a_2296_: *mut LeanObject,
    mut v_a_2297_: *mut LeanObject,
    mut v_a_2298_: *mut LeanObject,
    mut v_a_2299_: *mut LeanObject,
    mut v_a_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2301_: *mut LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar(
        v_fvarId_2293_,
        v_a_2294_,
        v_a_2295_,
        v_a_2296_,
        v_a_2297_,
        v_a_2298_,
        v_a_2299_,
    );
    lean_dec(v_a_2299_);
    lean_dec_ref(v_a_2298_);
    lean_dec(v_a_2297_);
    lean_dec_ref(v_a_2296_);
    lean_dec(v_a_2295_);
    lean_dec_ref(v_a_2294_);
    return v_res_2301_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(
    mut v_00_u03b2_2302_: *mut LeanObject,
    mut v_k_2303_: *mut LeanObject,
    mut v_t_2304_: *mut LeanObject,
) -> u8 {
    let mut v___x_2305_: u8 = 0;
    v___x_2305_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_2303_, v_t_2304_);
    return v___x_2305_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(
    mut v_00_u03b2_2306_: *mut LeanObject,
    mut v_k_2307_: *mut LeanObject,
    mut v_t_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2309_: u8 = 0;
    let mut v_r_2310_: *mut LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(v_00_u03b2_2306_, v_k_2307_, v_t_2308_);
    lean_dec(v_t_2308_);
    lean_dec(v_k_2307_);
    v_r_2310_ = lean_box((v_res_2309_) as usize);
    return v_r_2310_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(
    mut v_00_u03b2_2311_: *mut LeanObject,
    mut v_m_2312_: *mut LeanObject,
    mut v_a_2313_: *mut LeanObject,
    mut v_b_2314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2315_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_2312_, v_a_2313_, v_b_2314_);
    return v___x_2315_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(
    mut v_00_u03b2_2316_: *mut LeanObject,
    mut v_a_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
) -> u8 {
    let mut v___x_2319_: u8 = 0;
    v___x_2319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_2317_, v_x_2318_);
    return v___x_2319_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(
    mut v_00_u03b2_2320_: *mut LeanObject,
    mut v_a_2321_: *mut LeanObject,
    mut v_x_2322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2323_: u8 = 0;
    let mut v_r_2324_: *mut LeanObject = core::ptr::null_mut();
    v_res_2323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(v_00_u03b2_2320_, v_a_2321_, v_x_2322_);
    lean_dec(v_x_2322_);
    lean_dec(v_a_2321_);
    v_r_2324_ = lean_box((v_res_2323_) as usize);
    return v_r_2324_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2(
    mut v_00_u03b2_2325_: *mut LeanObject,
    mut v_data_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_data_2326_);
    return v___x_2327_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2328_: *mut LeanObject,
    mut v_i_2329_: *mut LeanObject,
    mut v_source_2330_: *mut LeanObject,
    mut v_target_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    v___x_2332_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v_i_2329_, v_source_2330_, v_target_2331_);
    return v___x_2332_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2333_: *mut LeanObject,
    mut v_x_2334_: *mut LeanObject,
    mut v_x_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2334_, v_x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(
    mut v_arg_2337_: *mut LeanObject,
    mut v_a_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_arg_2337_) == 1 {
        let mut v_fvarId_2341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_2341_ = lean_ctor_get(v_arg_2337_, 0);
        lean_inc(v_fvarId_2341_);
        lean_dec_ref_known(v_arg_2337_, 1);
        v___x_2342_ =
            l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_2341_, v_a_2338_, v_a_2339_);
        return v___x_2342_;
    } else {
        let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_arg_2337_);
        v___x_2343_ = lean_box(0);
        v___x_2344_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2344_, 0, v___x_2343_);
        return v___x_2344_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(
    mut v_arg_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
    mut v_a_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2349_: *mut LeanObject = core::ptr::null_mut();
    v_res_2349_ =
        l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_2345_, v_a_2346_, v_a_2347_);
    lean_dec(v_a_2347_);
    lean_dec_ref(v_a_2346_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg(
    mut v_arg_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
    mut v_a_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    v___x_2358_ =
        l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_2350_, v_a_2351_, v_a_2352_);
    return v___x_2358_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(
    mut v_arg_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_a_2361_: *mut LeanObject,
    mut v_a_2362_: *mut LeanObject,
    mut v_a_2363_: *mut LeanObject,
    mut v_a_2364_: *mut LeanObject,
    mut v_a_2365_: *mut LeanObject,
    mut v_a_2366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2367_: *mut LeanObject = core::ptr::null_mut();
    v_res_2367_ = l_Lean_Compiler_LCNF_FindUsed_visitArg(
        v_arg_2359_,
        v_a_2360_,
        v_a_2361_,
        v_a_2362_,
        v_a_2363_,
        v_a_2364_,
        v_a_2365_,
    );
    lean_dec(v_a_2365_);
    lean_dec_ref(v_a_2364_);
    lean_dec(v_a_2363_);
    lean_dec_ref(v_a_2362_);
    lean_dec(v_a_2361_);
    lean_dec_ref(v_a_2360_);
    return v_res_2367_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(
    mut v_as_2368_: *mut LeanObject,
    mut v_sz_2369_: usize,
    mut v_i_2370_: usize,
    mut v_b_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: usize = 0;
    let mut v___x_2378_: usize = 0;
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2389_: u8 = 0;
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v_reuseFailAlloc_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2409_: u8 = 0;
    let mut v_unused_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2380_ = lean_usize_dec_lt(v_i_2370_, v_sz_2369_);
                if v___x_2380_ == 0 {
                    v___x_2381_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2381_, 0, v_b_2371_);
                    return v___x_2381_;
                } else {
                    v_array_2382_ = lean_ctor_get(v_b_2371_, 0);
                    v_start_2383_ = lean_ctor_get(v_b_2371_, 1);
                    v_stop_2384_ = lean_ctor_get(v_b_2371_, 2);
                    v___x_2385_ = lean_nat_dec_lt(v_start_2383_, v_stop_2384_);
                    if v___x_2385_ == 0 {
                        v___x_2386_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2386_, 0, v_b_2371_);
                        return v___x_2386_;
                    } else {
                        lean_inc(v_stop_2384_);
                        lean_inc(v_start_2383_);
                        lean_inc_ref(v_array_2382_);
                        v_isSharedCheck_2409_ = (!lean_is_exclusive(v_b_2371_)) as u8;
                        if v_isSharedCheck_2409_ == 0 {
                            v_unused_2410_ = lean_ctor_get(v_b_2371_, 2);
                            lean_dec(v_unused_2410_);
                            v_unused_2411_ = lean_ctor_get(v_b_2371_, 1);
                            lean_dec(v_unused_2411_);
                            v_unused_2412_ = lean_ctor_get(v_b_2371_, 0);
                            lean_dec(v_unused_2412_);
                            v___x_2388_ = v_b_2371_;
                            v_isShared_2389_ = v_isSharedCheck_2409_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_b_2371_);
                            v___x_2388_ = lean_box(0);
                            v_isShared_2389_ = v_isSharedCheck_2409_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2377_ = 1usize;
                v___x_2378_ = lean_usize_add(v_i_2370_, v___x_2377_);
                v_i_2370_ = v___x_2378_;
                v_b_2371_ = v_a_2376_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2390_ = lean_array_fget(v_array_2382_, v_start_2383_);
                v___x_2391_ = lean_unsigned_to_nat(1);
                v___x_2392_ = lean_nat_add(v_start_2383_, v___x_2391_);
                lean_dec(v_start_2383_);
                if v_isShared_2389_ == 0 {
                    lean_ctor_set(v___x_2388_, 1, v___x_2392_);
                    v___x_2394_ = v___x_2388_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_array_2382_);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2392_);
                    lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_stop_2384_);
                    v___x_2394_ = v_reuseFailAlloc_2408_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v___x_2390_) == 1 {
                    v_fvarId_2395_ = lean_ctor_get(v___x_2390_, 0);
                    lean_inc(v_fvarId_2395_);
                    lean_dec_ref_known(v___x_2390_, 1);
                    v_a_2396_ = lean_array_uget_borrowed(v_as_2368_, v_i_2370_);
                    v_fvarId_2397_ = lean_ctor_get(v_a_2396_, 0);
                    v___x_2398_ = l_Lean_instBEqFVarId_beq(v_fvarId_2395_, v_fvarId_2397_);
                    if v___x_2398_ == 0 {
                        v___x_2399_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                            v_fvarId_2395_,
                            v___y_2372_,
                            v___y_2373_,
                        );
                        if lean_obj_tag(v___x_2399_) == 0 {
                            lean_dec_ref_known(v___x_2399_, 1);
                            v_a_2376_ = v___x_2394_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v___x_2394_);
                            v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
                            v_isSharedCheck_2407_ = (!lean_is_exclusive(v___x_2399_)) as u8;
                            if v_isSharedCheck_2407_ == 0 {
                                v___x_2402_ = v___x_2399_;
                                v_isShared_2403_ = v_isSharedCheck_2407_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2400_);
                                lean_dec(v___x_2399_);
                                v___x_2402_ = lean_box(0);
                                v_isShared_2403_ = v_isSharedCheck_2407_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_fvarId_2395_);
                        v_a_2376_ = v___x_2394_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2390_);
                    v_a_2376_ = v___x_2394_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v_isShared_2403_ == 0 {
                    v___x_2405_ = v___x_2402_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
                    v___x_2405_ = v_reuseFailAlloc_2406_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(
    mut v_as_2413_: *mut LeanObject,
    mut v_sz_2414_: *mut LeanObject,
    mut v_i_2415_: *mut LeanObject,
    mut v_b_2416_: *mut LeanObject,
    mut v___y_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2420_: usize = 0;
    let mut v_i_boxed_2421_: usize = 0;
    let mut v_res_2422_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2420_ = lean_unbox_usize(v_sz_2414_);
    lean_dec(v_sz_2414_);
    v_i_boxed_2421_ = lean_unbox_usize(v_i_2415_);
    lean_dec(v_i_2415_);
    v_res_2422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_2413_, v_sz_boxed_2420_, v_i_boxed_2421_, v_b_2416_, v___y_2417_, v___y_2418_);
    lean_dec(v___y_2418_);
    lean_dec_ref(v___y_2417_);
    lean_dec_ref(v_as_2413_);
    return v_res_2422_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(
    mut v_a_2423_: *mut LeanObject,
    mut v_b_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2434_: u8 = 0;
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2428_ = lean_ctor_get(v_a_2423_, 0);
                v_start_2429_ = lean_ctor_get(v_a_2423_, 1);
                v_stop_2430_ = lean_ctor_get(v_a_2423_, 2);
                v_isSharedCheck_2446_ = (!lean_is_exclusive(v_a_2423_)) as u8;
                if v_isSharedCheck_2446_ == 0 {
                    v___x_2432_ = v_a_2423_;
                    v_isShared_2433_ = v_isSharedCheck_2446_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_2430_);
                    lean_inc(v_start_2429_);
                    lean_inc(v_array_2428_);
                    lean_dec(v_a_2423_);
                    v___x_2432_ = lean_box(0);
                    v_isShared_2433_ = v_isSharedCheck_2446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2434_ = lean_nat_dec_lt(v_start_2429_, v_stop_2430_);
                if v___x_2434_ == 0 {
                    lean_del_object(v___x_2432_);
                    lean_dec(v_stop_2430_);
                    lean_dec(v_start_2429_);
                    lean_dec_ref(v_array_2428_);
                    v___x_2435_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2435_, 0, v_b_2424_);
                    return v___x_2435_;
                } else {
                    v___x_2436_ = lean_array_fget_borrowed(v_array_2428_, v_start_2429_);
                    v_fvarId_2437_ = lean_ctor_get(v___x_2436_, 0);
                    lean_inc(v_fvarId_2437_);
                    v___x_2438_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_fvarId_2437_,
                        v___y_2425_,
                        v___y_2426_,
                    );
                    if lean_obj_tag(v___x_2438_) == 0 {
                        lean_dec_ref_known(v___x_2438_, 1);
                        v___x_2439_ = lean_box(0);
                        v___x_2440_ = lean_unsigned_to_nat(1);
                        v___x_2441_ = lean_nat_add(v_start_2429_, v___x_2440_);
                        lean_dec(v_start_2429_);
                        if v_isShared_2433_ == 0 {
                            lean_ctor_set(v___x_2432_, 1, v___x_2441_);
                            v___x_2443_ = v___x_2432_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_array_2428_);
                            lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2441_);
                            lean_ctor_set(v_reuseFailAlloc_2445_, 2, v_stop_2430_);
                            v___x_2443_ = v_reuseFailAlloc_2445_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2432_);
                        lean_dec(v_stop_2430_);
                        lean_dec(v_start_2429_);
                        lean_dec_ref(v_array_2428_);
                        return v___x_2438_;
                    }
                }
            }
            2 => {
                v_a_2423_ = v___x_2443_;
                v_b_2424_ = v___x_2439_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(
    mut v_a_2447_: *mut LeanObject,
    mut v_b_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
    mut v___y_2450_: *mut LeanObject,
    mut v___y_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2452_: *mut LeanObject = core::ptr::null_mut();
    v_res_2452_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_2447_, v_b_2448_, v___y_2449_, v___y_2450_);
    lean_dec(v___y_2450_);
    lean_dec_ref(v___y_2449_);
    return v_res_2452_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(
    mut v_as_2453_: *mut LeanObject,
    mut v_i_2454_: usize,
    mut v_stop_2455_: usize,
    mut v_b_2456_: *mut LeanObject,
    mut v___y_2457_: *mut LeanObject,
    mut v___y_2458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: usize = 0;
    let mut v___x_2465_: usize = 0;
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2460_ = lean_usize_dec_eq(v_i_2454_, v_stop_2455_);
                if v___x_2460_ == 0 {
                    v___x_2461_ = lean_array_uget_borrowed(v_as_2453_, v_i_2454_);
                    lean_inc(v___x_2461_);
                    v___x_2462_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(
                        v___x_2461_,
                        v___y_2457_,
                        v___y_2458_,
                    );
                    if lean_obj_tag(v___x_2462_) == 0 {
                        v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
                        lean_inc(v_a_2463_);
                        lean_dec_ref_known(v___x_2462_, 1);
                        v___x_2464_ = 1usize;
                        v___x_2465_ = lean_usize_add(v_i_2454_, v___x_2464_);
                        v_i_2454_ = v___x_2465_;
                        v_b_2456_ = v_a_2463_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2462_;
                    }
                } else {
                    v___x_2467_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2467_, 0, v_b_2456_);
                    return v___x_2467_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(
    mut v_as_2468_: *mut LeanObject,
    mut v_i_2469_: *mut LeanObject,
    mut v_stop_2470_: *mut LeanObject,
    mut v_b_2471_: *mut LeanObject,
    mut v___y_2472_: *mut LeanObject,
    mut v___y_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2475_: usize = 0;
    let mut v_stop_boxed_2476_: usize = 0;
    let mut v_res_2477_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2475_ = lean_unbox_usize(v_i_2469_);
    lean_dec(v_i_2469_);
    v_stop_boxed_2476_ = lean_unbox_usize(v_stop_2470_);
    lean_dec(v_stop_2470_);
    v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_2468_, v_i_boxed_2475_, v_stop_boxed_2476_, v_b_2471_, v___y_2472_, v___y_2473_);
    lean_dec(v___y_2473_);
    lean_dec_ref(v___y_2472_);
    lean_dec_ref(v_as_2468_);
    return v_res_2477_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(
    mut v_a_2478_: *mut LeanObject,
    mut v_b_2479_: *mut LeanObject,
    mut v___y_2480_: *mut LeanObject,
    mut v___y_2481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2483_ = lean_ctor_get(v_a_2478_, 0);
                v_start_2484_ = lean_ctor_get(v_a_2478_, 1);
                v_stop_2485_ = lean_ctor_get(v_a_2478_, 2);
                v_isSharedCheck_2500_ = (!lean_is_exclusive(v_a_2478_)) as u8;
                if v_isSharedCheck_2500_ == 0 {
                    v___x_2487_ = v_a_2478_;
                    v_isShared_2488_ = v_isSharedCheck_2500_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_2485_);
                    lean_inc(v_start_2484_);
                    lean_inc(v_array_2483_);
                    lean_dec(v_a_2478_);
                    v___x_2487_ = lean_box(0);
                    v_isShared_2488_ = v_isSharedCheck_2500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2489_ = lean_nat_dec_lt(v_start_2484_, v_stop_2485_);
                if v___x_2489_ == 0 {
                    lean_del_object(v___x_2487_);
                    lean_dec(v_stop_2485_);
                    lean_dec(v_start_2484_);
                    lean_dec_ref(v_array_2483_);
                    v___x_2490_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2490_, 0, v_b_2479_);
                    return v___x_2490_;
                } else {
                    v___x_2491_ = lean_array_fget_borrowed(v_array_2483_, v_start_2484_);
                    lean_inc(v___x_2491_);
                    v___x_2492_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(
                        v___x_2491_,
                        v___y_2480_,
                        v___y_2481_,
                    );
                    if lean_obj_tag(v___x_2492_) == 0 {
                        lean_dec_ref_known(v___x_2492_, 1);
                        v___x_2493_ = lean_box(0);
                        v___x_2494_ = lean_unsigned_to_nat(1);
                        v___x_2495_ = lean_nat_add(v_start_2484_, v___x_2494_);
                        lean_dec(v_start_2484_);
                        if v_isShared_2488_ == 0 {
                            lean_ctor_set(v___x_2487_, 1, v___x_2495_);
                            v___x_2497_ = v___x_2487_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_array_2483_);
                            lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2495_);
                            lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_stop_2485_);
                            v___x_2497_ = v_reuseFailAlloc_2499_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2487_);
                        lean_dec(v_stop_2485_);
                        lean_dec(v_start_2484_);
                        lean_dec_ref(v_array_2483_);
                        return v___x_2492_;
                    }
                }
            }
            2 => {
                v_a_2478_ = v___x_2497_;
                v_b_2479_ = v___x_2493_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(
    mut v_a_2501_: *mut LeanObject,
    mut v_b_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2506_: *mut LeanObject = core::ptr::null_mut();
    v_res_2506_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_2501_, v_b_2502_, v___y_2503_, v___y_2504_);
    lean_dec(v___y_2504_);
    lean_dec_ref(v___y_2503_);
    return v_res_2506_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitLetValue(
    mut v_e_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v_unused_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_unused_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: usize = 0;
    let mut v___x_2557_: usize = 0;
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: usize = 0;
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2565_: usize = 0;
    let mut v___x_2566_: usize = 0;
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v_a_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_fvarId_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: u8 = 0;
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: usize = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: usize = 0;
    let mut v___x_2607_: usize = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut v_unused_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_e_2507_) {
                0 => {
                    v_isSharedCheck_2522_ = (!lean_is_exclusive(v_e_2507_)) as u8;
                    if v_isSharedCheck_2522_ == 0 {
                        v_unused_2523_ = lean_ctor_get(v_e_2507_, 0);
                        lean_dec(v_unused_2523_);
                        v___x_2516_ = v_e_2507_;
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_e_2507_);
                        v___x_2516_ = lean_box(0);
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2524_ = lean_box(0);
                    v___x_2525_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2525_, 0, v___x_2524_);
                    return v___x_2525_;
                }
                2 => {
                    v_struct_2526_ = lean_ctor_get(v_e_2507_, 2);
                    lean_inc(v_struct_2526_);
                    lean_dec_ref_known(v_e_2507_, 3);
                    v___x_2527_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_struct_2526_,
                        v_a_2508_,
                        v_a_2509_,
                    );
                    return v___x_2527_;
                }
                3 => {
                    v_decl_2528_ = lean_ctor_get(v_a_2508_, 0);
                    v_toSignature_2529_ = lean_ctor_get(v_decl_2528_, 0);
                    v_declName_2530_ = lean_ctor_get(v_e_2507_, 0);
                    lean_inc(v_declName_2530_);
                    v_args_2531_ = lean_ctor_get(v_e_2507_, 2);
                    lean_inc_ref(v_args_2531_);
                    lean_dec_ref_known(v_e_2507_, 3);
                    v_name_2532_ = lean_ctor_get(v_toSignature_2529_, 0);
                    v_params_2533_ = lean_ctor_get(v_toSignature_2529_, 3);
                    v___x_2548_ = lean_name_eq(v_declName_2530_, v_name_2532_);
                    lean_dec(v_declName_2530_);
                    if v___x_2548_ == 0 {
                        v___x_2549_ = lean_unsigned_to_nat(0);
                        v___x_2550_ = lean_array_get_size(v_args_2531_);
                        v___x_2551_ = lean_box(0);
                        v___x_2552_ = lean_nat_dec_lt(v___x_2549_, v___x_2550_);
                        if v___x_2552_ == 0 {
                            lean_dec_ref(v_args_2531_);
                            v___x_2553_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2553_, 0, v___x_2551_);
                            return v___x_2553_;
                        } else {
                            v___x_2554_ = lean_nat_dec_le(v___x_2550_, v___x_2550_);
                            if v___x_2554_ == 0 {
                                if v___x_2552_ == 0 {
                                    lean_dec_ref(v_args_2531_);
                                    v___x_2555_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_2555_, 0, v___x_2551_);
                                    return v___x_2555_;
                                } else {
                                    v___x_2556_ = 0usize;
                                    v___x_2557_ = lean_usize_of_nat(v___x_2550_);
                                    v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2531_, v___x_2556_, v___x_2557_, v___x_2551_, v_a_2508_, v_a_2509_);
                                    lean_dec_ref(v_args_2531_);
                                    return v___x_2558_;
                                }
                            } else {
                                v___x_2559_ = 0usize;
                                v___x_2560_ = lean_usize_of_nat(v___x_2550_);
                                v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2531_, v___x_2559_, v___x_2560_, v___x_2551_, v_a_2508_, v_a_2509_);
                                lean_dec_ref(v_args_2531_);
                                return v___x_2561_;
                            }
                        }
                    } else {
                        v___x_2562_ = lean_unsigned_to_nat(0);
                        v___x_2563_ = lean_array_get_size(v_args_2531_);
                        lean_inc_ref(v_args_2531_);
                        v___x_2564_ =
                            l_Array_toSubarray___redArg(v_args_2531_, v___x_2562_, v___x_2563_);
                        v_sz_2565_ = lean_array_size(v_params_2533_);
                        v___x_2566_ = 0usize;
                        v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_2533_, v_sz_2565_, v___x_2566_, v___x_2564_, v_a_2508_, v_a_2509_);
                        if lean_obj_tag(v___x_2567_) == 0 {
                            lean_dec_ref_known(v___x_2567_, 1);
                            v___x_2576_ = lean_array_get_size(v_params_2533_);
                            v___x_2577_ = lean_nat_dec_le(v___x_2576_, v___x_2562_);
                            if v___x_2577_ == 0 {
                                v_lower_2569_ = v___x_2576_;
                                v_upper_2570_ = v___x_2563_;
                                state = 6;
                                continue;
                            } else {
                                v_lower_2569_ = v___x_2562_;
                                v_upper_2570_ = v___x_2563_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_args_2531_);
                            v_a_2578_ = lean_ctor_get(v___x_2567_, 0);
                            v_isSharedCheck_2585_ = (!lean_is_exclusive(v___x_2567_)) as u8;
                            if v_isSharedCheck_2585_ == 0 {
                                v___x_2580_ = v___x_2567_;
                                v_isShared_2581_ = v_isSharedCheck_2585_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2578_);
                                lean_dec(v___x_2567_);
                                v___x_2580_ = lean_box(0);
                                v_isShared_2581_ = v_isSharedCheck_2585_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    v_fvarId_2586_ = lean_ctor_get(v_e_2507_, 0);
                    lean_inc(v_fvarId_2586_);
                    v_args_2587_ = lean_ctor_get(v_e_2507_, 1);
                    lean_inc_ref(v_args_2587_);
                    lean_dec_ref_known(v_e_2507_, 2);
                    v___x_2588_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_fvarId_2586_,
                        v_a_2508_,
                        v_a_2509_,
                    );
                    v_isSharedCheck_2609_ = (!lean_is_exclusive(v___x_2588_)) as u8;
                    if v_isSharedCheck_2609_ == 0 {
                        v_unused_2610_ = lean_ctor_get(v___x_2588_, 0);
                        lean_dec(v_unused_2610_);
                        v___x_2590_ = v___x_2588_;
                        v_isShared_2591_ = v_isSharedCheck_2609_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_2588_);
                        v___x_2590_ = lean_box(0);
                        v_isShared_2591_ = v_isSharedCheck_2609_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2518_ = lean_box(0);
                if v_isShared_2517_ == 0 {
                    lean_ctor_set(v___x_2516_, 0, v___x_2518_);
                    v___x_2520_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
                    v___x_2520_ = v_reuseFailAlloc_2521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2520_;
            }
            3 => {
                lean_inc_ref(v_params_2533_);
                v___x_2538_ =
                    l_Array_toSubarray___redArg(v_params_2533_, v_lower_2536_, v_upper_2537_);
                v___x_2539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v___x_2538_, v___y_2535_, v_a_2508_, v_a_2509_);
                if lean_obj_tag(v___x_2539_) == 0 {
                    v_isSharedCheck_2546_ = (!lean_is_exclusive(v___x_2539_)) as u8;
                    if v_isSharedCheck_2546_ == 0 {
                        v_unused_2547_ = lean_ctor_get(v___x_2539_, 0);
                        lean_dec(v_unused_2547_);
                        v___x_2541_ = v___x_2539_;
                        v_isShared_2542_ = v_isSharedCheck_2546_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_2539_);
                        v___x_2541_ = lean_box(0);
                        v_isShared_2542_ = v_isSharedCheck_2546_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___x_2539_;
                }
            }
            4 => {
                if v_isShared_2542_ == 0 {
                    lean_ctor_set(v___x_2541_, 0, v___y_2535_);
                    v___x_2544_ = v___x_2541_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___y_2535_);
                    v___x_2544_ = v_reuseFailAlloc_2545_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2544_;
            }
            6 => {
                v___x_2571_ =
                    l_Array_toSubarray___redArg(v_args_2531_, v_lower_2569_, v_upper_2570_);
                v___x_2572_ = lean_box(0);
                v___x_2573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_2571_, v___x_2572_, v_a_2508_, v_a_2509_);
                if lean_obj_tag(v___x_2573_) == 0 {
                    lean_dec_ref_known(v___x_2573_, 1);
                    v___x_2574_ = lean_array_get_size(v_params_2533_);
                    v___x_2575_ = lean_nat_dec_le(v___x_2563_, v___x_2562_);
                    if v___x_2575_ == 0 {
                        v___y_2535_ = v___x_2572_;
                        v_lower_2536_ = v___x_2563_;
                        v_upper_2537_ = v___x_2574_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2535_ = v___x_2572_;
                        v_lower_2536_ = v___x_2562_;
                        v_upper_2537_ = v___x_2574_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_2573_;
                }
            }
            7 => {
                if v_isShared_2581_ == 0 {
                    v___x_2583_ = v___x_2580_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2583_;
            }
            9 => {
                v___x_2592_ = lean_unsigned_to_nat(0);
                v___x_2593_ = lean_array_get_size(v_args_2587_);
                v___x_2594_ = lean_box(0);
                v___x_2595_ = lean_nat_dec_lt(v___x_2592_, v___x_2593_);
                if v___x_2595_ == 0 {
                    lean_dec_ref(v_args_2587_);
                    if v_isShared_2591_ == 0 {
                        lean_ctor_set(v___x_2590_, 0, v___x_2594_);
                        v___x_2597_ = v___x_2590_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2594_);
                        v___x_2597_ = v_reuseFailAlloc_2598_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_2599_ = lean_nat_dec_le(v___x_2593_, v___x_2593_);
                    if v___x_2599_ == 0 {
                        if v___x_2595_ == 0 {
                            lean_dec_ref(v_args_2587_);
                            if v_isShared_2591_ == 0 {
                                lean_ctor_set(v___x_2590_, 0, v___x_2594_);
                                v___x_2601_ = v___x_2590_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2594_);
                                v___x_2601_ = v_reuseFailAlloc_2602_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2590_);
                            v___x_2603_ = 0usize;
                            v___x_2604_ = lean_usize_of_nat(v___x_2593_);
                            v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2587_, v___x_2603_, v___x_2604_, v___x_2594_, v_a_2508_, v_a_2509_);
                            lean_dec_ref(v_args_2587_);
                            return v___x_2605_;
                        }
                    } else {
                        lean_del_object(v___x_2590_);
                        v___x_2606_ = 0usize;
                        v___x_2607_ = lean_usize_of_nat(v___x_2593_);
                        v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2587_, v___x_2606_, v___x_2607_, v___x_2594_, v_a_2508_, v_a_2509_);
                        lean_dec_ref(v_args_2587_);
                        return v___x_2608_;
                    }
                }
            }
            10 => {
                return v___x_2597_;
            }
            11 => {
                return v___x_2601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(
    mut v_e_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
    mut v_a_2615_: *mut LeanObject,
    mut v_a_2616_: *mut LeanObject,
    mut v_a_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2619_: *mut LeanObject = core::ptr::null_mut();
    v_res_2619_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(
        v_e_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_,
    );
    lean_dec(v_a_2617_);
    lean_dec_ref(v_a_2616_);
    lean_dec(v_a_2615_);
    lean_dec_ref(v_a_2614_);
    lean_dec(v_a_2613_);
    lean_dec_ref(v_a_2612_);
    return v_res_2619_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(
    mut v_as_2620_: *mut LeanObject,
    mut v_i_2621_: usize,
    mut v_stop_2622_: usize,
    mut v_b_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_2620_, v_i_2621_, v_stop_2622_, v_b_2623_, v___y_2624_, v___y_2625_);
    return v___x_2631_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(
    mut v_as_2632_: *mut LeanObject,
    mut v_i_2633_: *mut LeanObject,
    mut v_stop_2634_: *mut LeanObject,
    mut v_b_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
    mut v___y_2639_: *mut LeanObject,
    mut v___y_2640_: *mut LeanObject,
    mut v___y_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2643_: usize = 0;
    let mut v_stop_boxed_2644_: usize = 0;
    let mut v_res_2645_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2643_ = lean_unbox_usize(v_i_2633_);
    lean_dec(v_i_2633_);
    v_stop_boxed_2644_ = lean_unbox_usize(v_stop_2634_);
    lean_dec(v_stop_2634_);
    v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_2632_, v_i_boxed_2643_, v_stop_boxed_2644_, v_b_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
    lean_dec(v___y_2641_);
    lean_dec_ref(v___y_2640_);
    lean_dec(v___y_2639_);
    lean_dec_ref(v___y_2638_);
    lean_dec(v___y_2637_);
    lean_dec_ref(v___y_2636_);
    lean_dec_ref(v_as_2632_);
    return v_res_2645_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(
    mut v_as_2646_: *mut LeanObject,
    mut v_sz_2647_: usize,
    mut v_i_2648_: usize,
    mut v_b_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
    mut v___y_2651_: *mut LeanObject,
    mut v___y_2652_: *mut LeanObject,
    mut v___y_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_2646_, v_sz_2647_, v_i_2648_, v_b_2649_, v___y_2650_, v___y_2651_);
    return v___x_2657_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(
    mut v_as_2658_: *mut LeanObject,
    mut v_sz_2659_: *mut LeanObject,
    mut v_i_2660_: *mut LeanObject,
    mut v_b_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
    mut v___y_2668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2669_: usize = 0;
    let mut v_i_boxed_2670_: usize = 0;
    let mut v_res_2671_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2669_ = lean_unbox_usize(v_sz_2659_);
    lean_dec(v_sz_2659_);
    v_i_boxed_2670_ = lean_unbox_usize(v_i_2660_);
    lean_dec(v_i_2660_);
    v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_2658_, v_sz_boxed_2669_, v_i_boxed_2670_, v_b_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
    lean_dec(v___y_2667_);
    lean_dec_ref(v___y_2666_);
    lean_dec(v___y_2665_);
    lean_dec_ref(v___y_2664_);
    lean_dec(v___y_2663_);
    lean_dec_ref(v___y_2662_);
    lean_dec_ref(v_as_2658_);
    return v_res_2671_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(
    mut v_inst_2672_: *mut LeanObject,
    mut v_R_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_b_2675_: *mut LeanObject,
    mut v_c_2676_: *mut LeanObject,
    mut v___y_2677_: *mut LeanObject,
    mut v___y_2678_: *mut LeanObject,
    mut v___y_2679_: *mut LeanObject,
    mut v___y_2680_: *mut LeanObject,
    mut v___y_2681_: *mut LeanObject,
    mut v___y_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    v___x_2684_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_2674_, v_b_2675_, v___y_2677_, v___y_2678_);
    return v___x_2684_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(
    mut v_inst_2685_: *mut LeanObject,
    mut v_R_2686_: *mut LeanObject,
    mut v_a_2687_: *mut LeanObject,
    mut v_b_2688_: *mut LeanObject,
    mut v_c_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2697_: *mut LeanObject = core::ptr::null_mut();
    v_res_2697_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(
            v_inst_2685_,
            v_R_2686_,
            v_a_2687_,
            v_b_2688_,
            v_c_2689_,
            v___y_2690_,
            v___y_2691_,
            v___y_2692_,
            v___y_2693_,
            v___y_2694_,
            v___y_2695_,
        );
    lean_dec(v___y_2695_);
    lean_dec_ref(v___y_2694_);
    lean_dec(v___y_2693_);
    lean_dec_ref(v___y_2692_);
    lean_dec(v___y_2691_);
    lean_dec_ref(v___y_2690_);
    return v_res_2697_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(
    mut v_inst_2698_: *mut LeanObject,
    mut v_R_2699_: *mut LeanObject,
    mut v_a_2700_: *mut LeanObject,
    mut v_b_2701_: *mut LeanObject,
    mut v_c_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    v___x_2710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_2700_, v_b_2701_, v___y_2703_, v___y_2704_);
    return v___x_2710_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(
    mut v_inst_2711_: *mut LeanObject,
    mut v_R_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
    mut v_b_2714_: *mut LeanObject,
    mut v_c_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2723_: *mut LeanObject = core::ptr::null_mut();
    v_res_2723_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(
            v_inst_2711_,
            v_R_2712_,
            v_a_2713_,
            v_b_2714_,
            v_c_2715_,
            v___y_2716_,
            v___y_2717_,
            v___y_2718_,
            v___y_2719_,
            v___y_2720_,
            v___y_2721_,
        );
    lean_dec(v___y_2721_);
    lean_dec_ref(v___y_2720_);
    lean_dec(v___y_2719_);
    lean_dec_ref(v___y_2718_);
    lean_dec(v___y_2717_);
    lean_dec_ref(v___y_2716_);
    return v_res_2723_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visit(
    mut v_code_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_a_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: usize = 0;
    let mut v___x_2761_: usize = 0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2769_: u8 = 0;
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: u8 = 0;
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: usize = 0;
    let mut v___x_2782_: usize = 0;
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: usize = 0;
    let mut v___x_2785_: usize = 0;
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_unused_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_unused_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_2724_) {
                0 => {
                    v_decl_2744_ = lean_ctor_get(v_code_2724_, 0);
                    lean_inc_ref(v_decl_2744_);
                    v_k_2745_ = lean_ctor_get(v_code_2724_, 1);
                    lean_inc_ref(v_k_2745_);
                    lean_dec_ref_known(v_code_2724_, 2);
                    v_value_2746_ = lean_ctor_get(v_decl_2744_, 3);
                    lean_inc(v_value_2746_);
                    lean_dec_ref(v_decl_2744_);
                    v___x_2747_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(
                        v_value_2746_,
                        v_a_2725_,
                        v_a_2726_,
                        v_a_2727_,
                        v_a_2728_,
                        v_a_2729_,
                        v_a_2730_,
                    );
                    if lean_obj_tag(v___x_2747_) == 0 {
                        lean_dec_ref_known(v___x_2747_, 1);
                        v_code_2724_ = v_k_2745_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_2745_);
                        return v___x_2747_;
                    }
                }
                3 => {
                    v_args_2749_ = lean_ctor_get(v_code_2724_, 1);
                    lean_inc_ref(v_args_2749_);
                    lean_dec_ref_known(v_code_2724_, 2);
                    v___x_2750_ = lean_unsigned_to_nat(0);
                    v___x_2751_ = lean_array_get_size(v_args_2749_);
                    v___x_2752_ = lean_box(0);
                    v___x_2753_ = lean_nat_dec_lt(v___x_2750_, v___x_2751_);
                    if v___x_2753_ == 0 {
                        lean_dec_ref(v_args_2749_);
                        v___x_2754_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2754_, 0, v___x_2752_);
                        return v___x_2754_;
                    } else {
                        v___x_2755_ = lean_nat_dec_le(v___x_2751_, v___x_2751_);
                        if v___x_2755_ == 0 {
                            if v___x_2753_ == 0 {
                                lean_dec_ref(v_args_2749_);
                                v___x_2756_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2756_, 0, v___x_2752_);
                                return v___x_2756_;
                            } else {
                                v___x_2757_ = 0usize;
                                v___x_2758_ = lean_usize_of_nat(v___x_2751_);
                                v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2749_, v___x_2757_, v___x_2758_, v___x_2752_, v_a_2725_, v_a_2726_);
                                lean_dec_ref(v_args_2749_);
                                return v___x_2759_;
                            }
                        } else {
                            v___x_2760_ = 0usize;
                            v___x_2761_ = lean_usize_of_nat(v___x_2751_);
                            v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2749_, v___x_2760_, v___x_2761_, v___x_2752_, v_a_2725_, v_a_2726_);
                            lean_dec_ref(v_args_2749_);
                            return v___x_2762_;
                        }
                    }
                }
                4 => {
                    v_cases_2763_ = lean_ctor_get(v_code_2724_, 0);
                    lean_inc_ref(v_cases_2763_);
                    lean_dec_ref_known(v_code_2724_, 1);
                    v_discr_2764_ = lean_ctor_get(v_cases_2763_, 2);
                    lean_inc(v_discr_2764_);
                    v_alts_2765_ = lean_ctor_get(v_cases_2763_, 3);
                    lean_inc_ref(v_alts_2765_);
                    lean_dec_ref(v_cases_2763_);
                    v___x_2766_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_discr_2764_,
                        v_a_2725_,
                        v_a_2726_,
                    );
                    if lean_obj_tag(v___x_2766_) == 0 {
                        v_isSharedCheck_2787_ = (!lean_is_exclusive(v___x_2766_)) as u8;
                        if v_isSharedCheck_2787_ == 0 {
                            v_unused_2788_ = lean_ctor_get(v___x_2766_, 0);
                            lean_dec(v_unused_2788_);
                            v___x_2768_ = v___x_2766_;
                            v_isShared_2769_ = v_isSharedCheck_2787_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_2766_);
                            v___x_2768_ = lean_box(0);
                            v_isShared_2769_ = v_isSharedCheck_2787_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_alts_2765_);
                        return v___x_2766_;
                    }
                }
                5 => {
                    v_fvarId_2789_ = lean_ctor_get(v_code_2724_, 0);
                    lean_inc(v_fvarId_2789_);
                    lean_dec_ref_known(v_code_2724_, 1);
                    v___x_2790_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_fvarId_2789_,
                        v_a_2725_,
                        v_a_2726_,
                    );
                    return v___x_2790_;
                }
                6 => {
                    v_isSharedCheck_2798_ = (!lean_is_exclusive(v_code_2724_)) as u8;
                    if v_isSharedCheck_2798_ == 0 {
                        v_unused_2799_ = lean_ctor_get(v_code_2724_, 0);
                        lean_dec(v_unused_2799_);
                        v___x_2792_ = v_code_2724_;
                        v_isShared_2793_ = v_isSharedCheck_2798_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_code_2724_);
                        v___x_2792_ = lean_box(0);
                        v_isShared_2793_ = v_isSharedCheck_2798_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_decl_2800_ = lean_ctor_get(v_code_2724_, 0);
                    lean_inc_ref(v_decl_2800_);
                    v_k_2801_ = lean_ctor_get(v_code_2724_, 1);
                    lean_inc_ref(v_k_2801_);
                    lean_dec_ref(v_code_2724_);
                    v_decl_2733_ = v_decl_2800_;
                    v_k_2734_ = v_k_2801_;
                    v___y_2735_ = v_a_2725_;
                    v___y_2736_ = v_a_2726_;
                    v___y_2737_ = v_a_2727_;
                    v___y_2738_ = v_a_2728_;
                    v___y_2739_ = v_a_2729_;
                    v___y_2740_ = v_a_2730_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v_value_2741_ = lean_ctor_get(v_decl_2733_, 4);
                lean_inc_ref(v_value_2741_);
                lean_dec_ref(v_decl_2733_);
                v___x_2742_ = l_Lean_Compiler_LCNF_FindUsed_visit(
                    v_value_2741_,
                    v___y_2735_,
                    v___y_2736_,
                    v___y_2737_,
                    v___y_2738_,
                    v___y_2739_,
                    v___y_2740_,
                );
                if lean_obj_tag(v___x_2742_) == 0 {
                    lean_dec_ref_known(v___x_2742_, 1);
                    v_code_2724_ = v_k_2734_;
                    v_a_2725_ = v___y_2735_;
                    v_a_2726_ = v___y_2736_;
                    v_a_2727_ = v___y_2737_;
                    v_a_2728_ = v___y_2738_;
                    v_a_2729_ = v___y_2739_;
                    v_a_2730_ = v___y_2740_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_k_2734_);
                    return v___x_2742_;
                }
            }
            2 => {
                v___x_2770_ = lean_unsigned_to_nat(0);
                v___x_2771_ = lean_array_get_size(v_alts_2765_);
                v___x_2772_ = lean_box(0);
                v___x_2773_ = lean_nat_dec_lt(v___x_2770_, v___x_2771_);
                if v___x_2773_ == 0 {
                    lean_dec_ref(v_alts_2765_);
                    if v_isShared_2769_ == 0 {
                        lean_ctor_set(v___x_2768_, 0, v___x_2772_);
                        v___x_2775_ = v___x_2768_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
                        v___x_2775_ = v_reuseFailAlloc_2776_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2777_ = lean_nat_dec_le(v___x_2771_, v___x_2771_);
                    if v___x_2777_ == 0 {
                        if v___x_2773_ == 0 {
                            lean_dec_ref(v_alts_2765_);
                            if v_isShared_2769_ == 0 {
                                lean_ctor_set(v___x_2768_, 0, v___x_2772_);
                                v___x_2779_ = v___x_2768_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2772_);
                                v___x_2779_ = v_reuseFailAlloc_2780_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2768_);
                            v___x_2781_ = 0usize;
                            v___x_2782_ = lean_usize_of_nat(v___x_2771_);
                            v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_2765_, v___x_2781_, v___x_2782_, v___x_2772_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
                            lean_dec_ref(v_alts_2765_);
                            return v___x_2783_;
                        }
                    } else {
                        lean_del_object(v___x_2768_);
                        v___x_2784_ = 0usize;
                        v___x_2785_ = lean_usize_of_nat(v___x_2771_);
                        v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_2765_, v___x_2784_, v___x_2785_, v___x_2772_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
                        lean_dec_ref(v_alts_2765_);
                        return v___x_2786_;
                    }
                }
            }
            3 => {
                return v___x_2775_;
            }
            4 => {
                return v___x_2779_;
            }
            5 => {
                v___x_2794_ = lean_box(0);
                if v_isShared_2793_ == 0 {
                    lean_ctor_set_tag(v___x_2792_, 0);
                    lean_ctor_set(v___x_2792_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2792_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(
    mut v_as_2802_: *mut LeanObject,
    mut v_i_2803_: usize,
    mut v_stop_2804_: usize,
    mut v_b_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
    mut v___y_2808_: *mut LeanObject,
    mut v___y_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
    mut v___y_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: usize = 0;
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2820_ = lean_usize_dec_eq(v_i_2803_, v_stop_2804_);
                if v___x_2820_ == 0 {
                    v___x_2821_ = lean_array_uget_borrowed(v_as_2802_, v_i_2803_);
                    match lean_obj_tag(v___x_2821_) {
                        0 => {
                            v_code_2822_ = lean_ctor_get(v___x_2821_, 2);
                            lean_inc_ref(v_code_2822_);
                            v___y_2814_ = v_code_2822_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_2823_ = lean_ctor_get(v___x_2821_, 1);
                            lean_inc_ref(v_code_2823_);
                            v___y_2814_ = v_code_2823_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_2824_ = lean_ctor_get(v___x_2821_, 0);
                            lean_inc_ref(v_code_2824_);
                            v___y_2814_ = v_code_2824_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2825_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2825_, 0, v_b_2805_);
                    return v___x_2825_;
                }
            }
            1 => {
                v___x_2815_ = l_Lean_Compiler_LCNF_FindUsed_visit(
                    v___y_2814_,
                    v___y_2806_,
                    v___y_2807_,
                    v___y_2808_,
                    v___y_2809_,
                    v___y_2810_,
                    v___y_2811_,
                );
                if lean_obj_tag(v___x_2815_) == 0 {
                    v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
                    lean_inc(v_a_2816_);
                    lean_dec_ref_known(v___x_2815_, 1);
                    v___x_2817_ = 1usize;
                    v___x_2818_ = lean_usize_add(v_i_2803_, v___x_2817_);
                    v_i_2803_ = v___x_2818_;
                    v_b_2805_ = v_a_2816_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2815_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(
    mut v_as_2826_: *mut LeanObject,
    mut v_i_2827_: *mut LeanObject,
    mut v_stop_2828_: *mut LeanObject,
    mut v_b_2829_: *mut LeanObject,
    mut v___y_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
    mut v___y_2836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2837_: usize = 0;
    let mut v_stop_boxed_2838_: usize = 0;
    let mut v_res_2839_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2837_ = lean_unbox_usize(v_i_2827_);
    lean_dec(v_i_2827_);
    v_stop_boxed_2838_ = lean_unbox_usize(v_stop_2828_);
    lean_dec(v_stop_2828_);
    v_res_2839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_2826_, v_i_boxed_2837_, v_stop_boxed_2838_, v_b_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
    lean_dec(v___y_2835_);
    lean_dec_ref(v___y_2834_);
    lean_dec(v___y_2833_);
    lean_dec_ref(v___y_2832_);
    lean_dec(v___y_2831_);
    lean_dec_ref(v___y_2830_);
    lean_dec_ref(v_as_2826_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visit___boxed(
    mut v_code_2840_: *mut LeanObject,
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_a_2845_: *mut LeanObject,
    mut v_a_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2848_: *mut LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Lean_Compiler_LCNF_FindUsed_visit(
        v_code_2840_,
        v_a_2841_,
        v_a_2842_,
        v_a_2843_,
        v_a_2844_,
        v_a_2845_,
        v_a_2846_,
    );
    lean_dec(v_a_2846_);
    lean_dec_ref(v_a_2845_);
    lean_dec(v_a_2844_);
    lean_dec_ref(v_a_2843_);
    lean_dec(v_a_2842_);
    lean_dec_ref(v_a_2841_);
    return v_res_2848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(
    mut v_f_2849_: *mut LeanObject,
    mut v_v_2850_: *mut LeanObject,
    mut v___y_2851_: *mut LeanObject,
    mut v___y_2852_: *mut LeanObject,
    mut v___y_2853_: *mut LeanObject,
    mut v___y_2854_: *mut LeanObject,
    mut v___y_2855_: *mut LeanObject,
    mut v___y_2856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut v_unused_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_2850_) == 0 {
                    v_code_2858_ = lean_ctor_get(v_v_2850_, 0);
                    lean_inc_ref(v_code_2858_);
                    lean_dec_ref_known(v_v_2850_, 1);
                    lean_inc(v___y_2856_);
                    lean_inc_ref(v___y_2855_);
                    lean_inc(v___y_2854_);
                    lean_inc_ref(v___y_2853_);
                    lean_inc(v___y_2852_);
                    lean_inc_ref(v___y_2851_);
                    v___x_2859_ = lean_apply_8(
                        v_f_2849_,
                        v_code_2858_,
                        v___y_2851_,
                        v___y_2852_,
                        v___y_2853_,
                        v___y_2854_,
                        v___y_2855_,
                        v___y_2856_,
                        lean_box(0),
                    );
                    return v___x_2859_;
                } else {
                    lean_dec_ref(v_f_2849_);
                    v_isSharedCheck_2867_ = (!lean_is_exclusive(v_v_2850_)) as u8;
                    if v_isSharedCheck_2867_ == 0 {
                        v_unused_2868_ = lean_ctor_get(v_v_2850_, 0);
                        lean_dec(v_unused_2868_);
                        v___x_2861_ = v_v_2850_;
                        v_isShared_2862_ = v_isSharedCheck_2867_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_2850_);
                        v___x_2861_ = lean_box(0);
                        v_isShared_2862_ = v_isSharedCheck_2867_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2863_ = lean_box(0);
                if v_isShared_2862_ == 0 {
                    lean_ctor_set_tag(v___x_2861_, 0);
                    lean_ctor_set(v___x_2861_, 0, v___x_2863_);
                    v___x_2865_ = v___x_2861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
                    v___x_2865_ = v_reuseFailAlloc_2866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(
    mut v_f_2869_: *mut LeanObject,
    mut v_v_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
    mut v___y_2874_: *mut LeanObject,
    mut v___y_2875_: *mut LeanObject,
    mut v___y_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2878_: *mut LeanObject = core::ptr::null_mut();
    v_res_2878_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_2869_, v_v_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
    lean_dec(v___y_2876_);
    lean_dec_ref(v___y_2875_);
    lean_dec(v___y_2874_);
    lean_dec_ref(v___y_2873_);
    lean_dec(v___y_2872_);
    lean_dec_ref(v___y_2871_);
    return v_res_2878_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(
    mut v_pu_2879_: u8,
    mut v_f_2880_: *mut LeanObject,
    mut v_v_2881_: *mut LeanObject,
    mut v___y_2882_: *mut LeanObject,
    mut v___y_2883_: *mut LeanObject,
    mut v___y_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
    mut v___y_2886_: *mut LeanObject,
    mut v___y_2887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    v___x_2889_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_2880_, v_v_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    return v___x_2889_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(
    mut v_pu_2890_: *mut LeanObject,
    mut v_f_2891_: *mut LeanObject,
    mut v_v_2892_: *mut LeanObject,
    mut v___y_2893_: *mut LeanObject,
    mut v___y_2894_: *mut LeanObject,
    mut v___y_2895_: *mut LeanObject,
    mut v___y_2896_: *mut LeanObject,
    mut v___y_2897_: *mut LeanObject,
    mut v___y_2898_: *mut LeanObject,
    mut v___y_2899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2900_: u8 = 0;
    let mut v_res_2901_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2900_ = (lean_unbox(v_pu_2890_) as u8);
    v_res_2901_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_2900_, v_f_2891_, v_v_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
    lean_dec(v___y_2898_);
    lean_dec_ref(v___y_2897_);
    lean_dec(v___y_2896_);
    lean_dec_ref(v___y_2895_);
    lean_dec(v___y_2894_);
    lean_dec_ref(v___y_2893_);
    return v_res_2901_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(
    mut v_as_2902_: *mut LeanObject,
    mut v_i_2903_: usize,
    mut v_stop_2904_: usize,
    mut v_b_2905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: usize = 0;
    let mut v___x_2911_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2906_ = lean_usize_dec_eq(v_i_2903_, v_stop_2904_);
                if v___x_2906_ == 0 {
                    v___x_2907_ = lean_array_uget_borrowed(v_as_2902_, v_i_2903_);
                    v_fvarId_2908_ = lean_ctor_get(v___x_2907_, 0);
                    lean_inc(v_fvarId_2908_);
                    v___x_2909_ = l_Lean_FVarIdSet_insert(v_b_2905_, v_fvarId_2908_);
                    v___x_2910_ = 1usize;
                    v___x_2911_ = lean_usize_add(v_i_2903_, v___x_2910_);
                    v_i_2903_ = v___x_2911_;
                    v_b_2905_ = v___x_2909_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2905_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(
    mut v_as_2913_: *mut LeanObject,
    mut v_i_2914_: *mut LeanObject,
    mut v_stop_2915_: *mut LeanObject,
    mut v_b_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2917_: usize = 0;
    let mut v_stop_boxed_2918_: usize = 0;
    let mut v_res_2919_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2917_ = lean_unbox_usize(v_i_2914_);
    lean_dec(v_i_2914_);
    v_stop_boxed_2918_ = lean_unbox_usize(v_stop_2915_);
    lean_dec(v_stop_2915_);
    v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_2913_, v_i_boxed_2917_, v_stop_boxed_2918_, v_b_2916_);
    lean_dec_ref(v_as_2913_);
    return v_res_2919_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(
    mut v_decl_2921_: *mut LeanObject,
    mut v_a_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2945_: u8 = 0;
    let mut v_unused_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2954_: u8 = 0;
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: usize = 0;
    let mut v___x_2960_: usize = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: usize = 0;
    let mut v___x_2963_: usize = 0;
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_2927_ = lean_ctor_get(v_decl_2921_, 0);
                v_value_2928_ = lean_ctor_get(v_decl_2921_, 1);
                lean_inc_ref(v_value_2928_);
                v_params_2929_ = lean_ctor_get(v_toSignature_2927_, 3);
                v___x_2930_ = lean_box(1);
                v___x_2931_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v___x_2955_ = lean_unsigned_to_nat(0);
                v___x_2956_ = lean_array_get_size(v_params_2929_);
                v___x_2957_ = lean_nat_dec_lt(v___x_2955_, v___x_2956_);
                if v___x_2957_ == 0 {
                    v___y_2933_ = v___x_2930_;
                    state = 1;
                    continue;
                } else {
                    v___x_2958_ = lean_nat_dec_le(v___x_2956_, v___x_2956_);
                    if v___x_2958_ == 0 {
                        if v___x_2957_ == 0 {
                            v___y_2933_ = v___x_2930_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2959_ = 0usize;
                            v___x_2960_ = lean_usize_of_nat(v___x_2956_);
                            v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_2929_, v___x_2959_, v___x_2960_, v___x_2930_);
                            v___y_2933_ = v___x_2961_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2962_ = 0usize;
                        v___x_2963_ = lean_usize_of_nat(v___x_2956_);
                        v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_2929_, v___x_2962_, v___x_2963_, v___x_2930_);
                        v___y_2933_ = v___x_2964_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2934_ = lean_st_mk_ref(v___x_2931_);
                v___x_2935_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0;
                v___x_2936_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2936_, 0, v_decl_2921_);
                lean_ctor_set(v___x_2936_, 1, v___y_2933_);
                v___x_2937_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_2935_, v_value_2928_, v___x_2936_, v___x_2934_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
                lean_dec_ref_known(v___x_2936_, 2);
                if lean_obj_tag(v___x_2937_) == 0 {
                    v_isSharedCheck_2945_ = (!lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2945_ == 0 {
                        v_unused_2946_ = lean_ctor_get(v___x_2937_, 0);
                        lean_dec(v_unused_2946_);
                        v___x_2939_ = v___x_2937_;
                        v_isShared_2940_ = v_isSharedCheck_2945_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2937_);
                        v___x_2939_ = lean_box(0);
                        v_isShared_2940_ = v_isSharedCheck_2945_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2934_);
                    v_a_2947_ = lean_ctor_get(v___x_2937_, 0);
                    v_isSharedCheck_2954_ = (!lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2954_ == 0 {
                        v___x_2949_ = v___x_2937_;
                        v_isShared_2950_ = v_isSharedCheck_2954_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2947_);
                        lean_dec(v___x_2937_);
                        v___x_2949_ = lean_box(0);
                        v_isShared_2950_ = v_isSharedCheck_2954_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2941_ = lean_st_ref_get(v___x_2934_);
                lean_dec(v___x_2934_);
                if v_isShared_2940_ == 0 {
                    lean_ctor_set(v___x_2939_, 0, v___x_2941_);
                    v___x_2943_ = v___x_2939_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
                    v___x_2943_ = v_reuseFailAlloc_2944_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2943_;
            }
            4 => {
                if v_isShared_2950_ == 0 {
                    v___x_2952_ = v___x_2949_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
                    v___x_2952_ = v_reuseFailAlloc_2953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(
    mut v_decl_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2971_: *mut LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(
        v_decl_2965_,
        v_a_2966_,
        v_a_2967_,
        v_a_2968_,
        v_a_2969_,
    );
    lean_dec(v_a_2969_);
    lean_dec_ref(v_a_2968_);
    lean_dec(v_a_2967_);
    lean_dec_ref(v_a_2966_);
    return v_res_2971_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2972_: u8 = 0;
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    v___x_2972_ = 0;
    v___x_2973_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_2972_);
    return v___x_2973_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(
    mut v_msg_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___x_2975_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0,
    );
    v___x_2976_ = lean_panic_fn_borrowed(v___x_2975_, v_msg_2974_);
    return v___x_2976_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(
    mut v_args_2977_: *mut LeanObject,
    mut v_upperBound_2978_: *mut LeanObject,
    mut v___x_2979_: *mut LeanObject,
    mut v_a_2980_: *mut LeanObject,
    mut v_b_2981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_nat_dec_lt(v_a_2980_, v_upperBound_2978_);
                if v___x_2991_ == 0 {
                    lean_dec(v_a_2980_);
                    v___x_2992_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2992_, 0, v_b_2981_);
                    return v___x_2992_;
                } else {
                    v___x_2993_ = lean_array_get_size(v___x_2979_);
                    v___x_2994_ = lean_nat_dec_lt(v_a_2980_, v___x_2993_);
                    if v___x_2994_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_2995_ = lean_array_fget_borrowed(v___x_2979_, v_a_2980_);
                        v___x_2996_ = (lean_unbox(v___x_2995_) as u8);
                        if v___x_2996_ == 0 {
                            v_a_2984_ = v_b_2981_;
                            state = 1;
                            continue;
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2985_ = lean_unsigned_to_nat(1);
                v___x_2986_ = lean_nat_add(v_a_2980_, v___x_2985_);
                lean_dec(v_a_2980_);
                v_a_2980_ = v___x_2986_;
                v_b_2981_ = v_a_2984_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2989_ = lean_array_fget_borrowed(v_args_2977_, v_a_2980_);
                lean_inc(v___x_2989_);
                v___x_2990_ = lean_array_push(v_b_2981_, v___x_2989_);
                v_a_2984_ = v___x_2990_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(
    mut v_args_2997_: *mut LeanObject,
    mut v_upperBound_2998_: *mut LeanObject,
    mut v___x_2999_: *mut LeanObject,
    mut v_a_3000_: *mut LeanObject,
    mut v_b_3001_: *mut LeanObject,
    mut v___y_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3003_: *mut LeanObject = core::ptr::null_mut();
    v_res_3003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_2997_, v_upperBound_2998_, v___x_2999_, v_a_3000_, v_b_3001_);
    lean_dec_ref(v___x_2999_);
    lean_dec(v_upperBound_2998_);
    lean_dec_ref(v_args_2997_);
    return v_res_3003_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3() -> *mut LeanObject {
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    v___x_3007_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2;
    v___x_3008_ = lean_unsigned_to_nat(9);
    v___x_3009_ = lean_unsigned_to_nat(641);
    v___x_3010_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
    v___x_3011_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0;
    v___x_3012_ = l_mkPanicMessageWithDecl(
        v___x_3011_,
        v___x_3010_,
        v___x_3009_,
        v___x_3008_,
        v___x_3007_,
    );
    return v___x_3012_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ReduceArity_reduce(
    mut v_code_3015_: *mut LeanObject,
    mut v_a_3016_: *mut LeanObject,
    mut v_a_3017_: *mut LeanObject,
    mut v_a_3018_: *mut LeanObject,
    mut v_a_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3025_: u8 = 0;
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3032_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: usize = 0;
    let mut v___x_3057_: usize = 0;
    let mut v___x_3058_: u8 = 0;
    let mut v___x_3059_: usize = 0;
    let mut v___x_3060_: usize = 0;
    let mut v___x_3061_: u8 = 0;
    let mut v_a_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: usize = 0;
    let mut v___x_3069_: usize = 0;
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v_unused_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut v_decl_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3096_: u8 = 0;
    let mut v_declName_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclName_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramMask_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___y_3107_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3117_: u8 = 0;
    let mut v_unused_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: usize = 0;
    let mut v___x_3124_: usize = 0;
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: u8 = 0;
    let mut v_isSharedCheck_3128_: u8 = 0;
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v___y_3146_: u8 = 0;
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_unused_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: usize = 0;
    let mut v___x_3166_: usize = 0;
    let mut v___x_3167_: u8 = 0;
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_a_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v_reuseFailAlloc_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_unused_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___y_3195_: u8 = 0;
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_unused_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: usize = 0;
    let mut v___x_3212_: usize = 0;
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: usize = 0;
    let mut v___x_3215_: u8 = 0;
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut v_decl_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3234_: u8 = 0;
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut v_unused_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_a_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_3015_) {
                0 => {
                    v_decl_3089_ = lean_ctor_get(v_code_3015_, 0);
                    v_value_3090_ = lean_ctor_get(v_decl_3089_, 3);
                    lean_inc(v_value_3090_);
                    if lean_obj_tag(v_value_3090_) == 3 {
                        v_k_3091_ = lean_ctor_get(v_code_3015_, 1);
                        v_declName_3092_ = lean_ctor_get(v_value_3090_, 0);
                        v_args_3093_ = lean_ctor_get(v_value_3090_, 2);
                        v_isSharedCheck_3186_ = (!lean_is_exclusive(v_value_3090_)) as u8;
                        if v_isSharedCheck_3186_ == 0 {
                            v_unused_3187_ = lean_ctor_get(v_value_3090_, 1);
                            lean_dec(v_unused_3187_);
                            v___x_3095_ = v_value_3090_;
                            v_isShared_3096_ = v_isSharedCheck_3186_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_args_3093_);
                            lean_inc(v_declName_3092_);
                            lean_dec(v_value_3090_);
                            v___x_3095_ = lean_box(0);
                            v_isShared_3096_ = v_isSharedCheck_3186_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_value_3090_);
                        v_k_3188_ = lean_ctor_get(v_code_3015_, 1);
                        lean_inc_ref(v_k_3188_);
                        v___x_3189_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                            v_k_3188_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                        );
                        if lean_obj_tag(v___x_3189_) == 0 {
                            v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
                            v_isSharedCheck_3216_ = (!lean_is_exclusive(v___x_3189_)) as u8;
                            if v_isSharedCheck_3216_ == 0 {
                                v___x_3192_ = v___x_3189_;
                                v_isShared_3193_ = v_isSharedCheck_3216_;
                                state = 26;
                                continue;
                            } else {
                                lean_inc(v_a_3190_);
                                lean_dec(v___x_3189_);
                                v___x_3192_ = lean_box(0);
                                v_isShared_3193_ = v_isSharedCheck_3216_;
                                state = 26;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_code_3015_, 2);
                            return v___x_3189_;
                        }
                    }
                }
                1 => {
                    v_decl_3217_ = lean_ctor_get(v_code_3015_, 0);
                    v_k_3218_ = lean_ctor_get(v_code_3015_, 1);
                    lean_inc_ref(v_k_3218_);
                    lean_inc_ref(v_decl_3217_);
                    v_decl_3037_ = v_decl_3217_;
                    v_k_3038_ = v_k_3218_;
                    v___y_3039_ = v_a_3016_;
                    v___y_3040_ = v_a_3017_;
                    v___y_3041_ = v_a_3018_;
                    v___y_3042_ = v_a_3019_;
                    v___y_3043_ = v_a_3020_;
                    state = 3;
                    continue;
                }
                2 => {
                    v_decl_3219_ = lean_ctor_get(v_code_3015_, 0);
                    v_k_3220_ = lean_ctor_get(v_code_3015_, 1);
                    lean_inc_ref(v_k_3220_);
                    lean_inc_ref(v_decl_3219_);
                    v_decl_3037_ = v_decl_3219_;
                    v_k_3038_ = v_k_3220_;
                    v___y_3039_ = v_a_3016_;
                    v___y_3040_ = v_a_3017_;
                    v___y_3041_ = v_a_3018_;
                    v___y_3042_ = v_a_3019_;
                    v___y_3043_ = v_a_3020_;
                    state = 3;
                    continue;
                }
                4 => {
                    v_cases_3221_ = lean_ctor_get(v_code_3015_, 0);
                    lean_inc_ref(v_cases_3221_);
                    v_typeName_3222_ = lean_ctor_get(v_cases_3221_, 0);
                    v_resultType_3223_ = lean_ctor_get(v_cases_3221_, 1);
                    v_discr_3224_ = lean_ctor_get(v_cases_3221_, 2);
                    v_alts_3225_ = lean_ctor_get(v_cases_3221_, 3);
                    v_isSharedCheck_3264_ = (!lean_is_exclusive(v_cases_3221_)) as u8;
                    if v_isSharedCheck_3264_ == 0 {
                        v___x_3227_ = v_cases_3221_;
                        v_isShared_3228_ = v_isSharedCheck_3264_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_alts_3225_);
                        lean_inc(v_discr_3224_);
                        lean_inc(v_resultType_3223_);
                        lean_inc(v_typeName_3222_);
                        lean_dec(v_cases_3221_);
                        v___x_3227_ = lean_box(0);
                        v_isShared_3228_ = v_isSharedCheck_3264_;
                        state = 32;
                        continue;
                    }
                }
                _ => {
                    v___x_3265_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3265_, 0, v_code_3015_);
                    return v___x_3265_;
                }
            },
            1 => {
                if v___y_3025_ == 0 {
                    lean_dec_ref(v_code_3015_);
                    v___x_3026_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3026_, 0, v___y_3024_);
                    lean_ctor_set(v___x_3026_, 1, v___y_3023_);
                    v___x_3027_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3027_, 0, v___x_3026_);
                    return v___x_3027_;
                } else {
                    lean_dec_ref(v___y_3024_);
                    lean_dec_ref(v___y_3023_);
                    v___x_3028_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3028_, 0, v_code_3015_);
                    return v___x_3028_;
                }
            }
            2 => {
                if v___y_3032_ == 0 {
                    lean_dec_ref(v_code_3015_);
                    v___x_3033_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3033_, 0, v___y_3031_);
                    lean_ctor_set(v___x_3033_, 1, v___y_3030_);
                    v___x_3034_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3034_, 0, v___x_3033_);
                    return v___x_3034_;
                } else {
                    lean_dec_ref(v___y_3031_);
                    lean_dec_ref(v___y_3030_);
                    v___x_3035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3035_, 0, v_code_3015_);
                    return v___x_3035_;
                }
            }
            3 => {
                v_params_3044_ = lean_ctor_get(v_decl_3037_, 2);
                lean_inc_ref(v_params_3044_);
                v_type_3045_ = lean_ctor_get(v_decl_3037_, 3);
                lean_inc_ref(v_type_3045_);
                v_value_3046_ = lean_ctor_get(v_decl_3037_, 4);
                lean_inc_ref(v_value_3046_);
                v___x_3047_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                    v_value_3046_,
                    v___y_3039_,
                    v___y_3040_,
                    v___y_3041_,
                    v___y_3042_,
                    v___y_3043_,
                );
                if lean_obj_tag(v___x_3047_) == 0 {
                    v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
                    lean_inc(v_a_3048_);
                    lean_dec_ref_known(v___x_3047_, 1);
                    v___x_3049_ = 0;
                    v___x_3050_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3049_, v_decl_3037_, v_type_3045_, v_params_3044_, v_a_3048_, v___y_3041_);
                    if lean_obj_tag(v___x_3050_) == 0 {
                        v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
                        lean_inc(v_a_3051_);
                        lean_dec_ref_known(v___x_3050_, 1);
                        v___x_3052_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                            v_k_3038_,
                            v___y_3039_,
                            v___y_3040_,
                            v___y_3041_,
                            v___y_3042_,
                            v___y_3043_,
                        );
                        if lean_obj_tag(v___x_3052_) == 0 {
                            match lean_obj_tag(v_code_3015_) {
                                1 => {
                                    v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
                                    lean_inc(v_a_3053_);
                                    lean_dec_ref_known(v___x_3052_, 1);
                                    v_decl_3054_ = lean_ctor_get(v_code_3015_, 0);
                                    v_k_3055_ = lean_ctor_get(v_code_3015_, 1);
                                    v___x_3056_ = lean_ptr_addr(v_k_3055_);
                                    v___x_3057_ = lean_ptr_addr(v_a_3053_);
                                    v___x_3058_ = lean_usize_dec_eq(v___x_3056_, v___x_3057_);
                                    if v___x_3058_ == 0 {
                                        v___y_3023_ = v_a_3053_;
                                        v___y_3024_ = v_a_3051_;
                                        v___y_3025_ = v___x_3058_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3059_ = lean_ptr_addr(v_decl_3054_);
                                        v___x_3060_ = lean_ptr_addr(v_a_3051_);
                                        v___x_3061_ = lean_usize_dec_eq(v___x_3059_, v___x_3060_);
                                        v___y_3023_ = v_a_3053_;
                                        v___y_3024_ = v_a_3051_;
                                        v___y_3025_ = v___x_3061_;
                                        state = 1;
                                        continue;
                                    }
                                }
                                2 => {
                                    v_a_3062_ = lean_ctor_get(v___x_3052_, 0);
                                    lean_inc(v_a_3062_);
                                    lean_dec_ref_known(v___x_3052_, 1);
                                    v_decl_3063_ = lean_ctor_get(v_code_3015_, 0);
                                    v_k_3064_ = lean_ctor_get(v_code_3015_, 1);
                                    v___x_3065_ = lean_ptr_addr(v_k_3064_);
                                    v___x_3066_ = lean_ptr_addr(v_a_3062_);
                                    v___x_3067_ = lean_usize_dec_eq(v___x_3065_, v___x_3066_);
                                    if v___x_3067_ == 0 {
                                        v___y_3030_ = v_a_3062_;
                                        v___y_3031_ = v_a_3051_;
                                        v___y_3032_ = v___x_3067_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3068_ = lean_ptr_addr(v_decl_3063_);
                                        v___x_3069_ = lean_ptr_addr(v_a_3051_);
                                        v___x_3070_ = lean_usize_dec_eq(v___x_3068_, v___x_3069_);
                                        v___y_3030_ = v_a_3062_;
                                        v___y_3031_ = v_a_3051_;
                                        v___y_3032_ = v___x_3070_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                _ => {
                                    lean_dec(v_a_3051_);
                                    lean_dec_ref(v_code_3015_);
                                    v_isSharedCheck_3079_ = (!lean_is_exclusive(v___x_3052_)) as u8;
                                    if v_isSharedCheck_3079_ == 0 {
                                        v_unused_3080_ = lean_ctor_get(v___x_3052_, 0);
                                        lean_dec(v_unused_3080_);
                                        v___x_3072_ = v___x_3052_;
                                        v_isShared_3073_ = v_isSharedCheck_3079_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3052_);
                                        v___x_3072_ = lean_box(0);
                                        v_isShared_3073_ = v_isSharedCheck_3079_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_3051_);
                            lean_dec_ref(v_code_3015_);
                            return v___x_3052_;
                        }
                    } else {
                        lean_dec_ref(v_k_3038_);
                        lean_dec_ref(v_code_3015_);
                        v_a_3081_ = lean_ctor_get(v___x_3050_, 0);
                        v_isSharedCheck_3088_ = (!lean_is_exclusive(v___x_3050_)) as u8;
                        if v_isSharedCheck_3088_ == 0 {
                            v___x_3083_ = v___x_3050_;
                            v_isShared_3084_ = v_isSharedCheck_3088_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3081_);
                            lean_dec(v___x_3050_);
                            v___x_3083_ = lean_box(0);
                            v_isShared_3084_ = v_isSharedCheck_3088_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_3045_);
                    lean_dec_ref(v_params_3044_);
                    lean_dec_ref(v_k_3038_);
                    lean_dec_ref(v_decl_3037_);
                    lean_dec_ref(v_code_3015_);
                    return v___x_3047_;
                }
            }
            4 => {
                v___x_3074_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3,
                );
                v___x_3075_ =
                    l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_3074_);
                if v_isShared_3073_ == 0 {
                    lean_ctor_set(v___x_3072_, 0, v___x_3075_);
                    v___x_3077_ = v___x_3072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
                    v___x_3077_ = v_reuseFailAlloc_3078_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3077_;
            }
            6 => {
                if v_isShared_3084_ == 0 {
                    v___x_3086_ = v___x_3083_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
                    v___x_3086_ = v_reuseFailAlloc_3087_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3086_;
            }
            8 => {
                v_declName_3097_ = lean_ctor_get(v_a_3016_, 0);
                v_auxDeclName_3098_ = lean_ctor_get(v_a_3016_, 1);
                v_paramMask_3099_ = lean_ctor_get(v_a_3016_, 2);
                v___x_3100_ = lean_name_eq(v_declName_3092_, v_declName_3097_);
                lean_dec(v_declName_3092_);
                if v___x_3100_ == 0 {
                    lean_del_object(v___x_3095_);
                    lean_dec_ref(v_args_3093_);
                    lean_inc_ref(v_k_3091_);
                    v___x_3101_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                        v_k_3091_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3101_) == 0 {
                        v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
                        v_isSharedCheck_3128_ = (!lean_is_exclusive(v___x_3101_)) as u8;
                        if v_isSharedCheck_3128_ == 0 {
                            v___x_3104_ = v___x_3101_;
                            v_isShared_3105_ = v_isSharedCheck_3128_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3102_);
                            lean_dec(v___x_3101_);
                            v___x_3104_ = lean_box(0);
                            v_isShared_3105_ = v_isSharedCheck_3128_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_3015_, 2);
                        return v___x_3101_;
                    }
                } else {
                    v___x_3129_ = lean_array_get_size(v_args_3093_);
                    v___x_3130_ = lean_unsigned_to_nat(0);
                    v___x_3131_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
                    v___x_3132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_3093_, v___x_3129_, v_paramMask_3099_, v___x_3130_, v___x_3131_);
                    lean_dec_ref(v_args_3093_);
                    if lean_obj_tag(v___x_3132_) == 0 {
                        v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
                        lean_inc(v_a_3133_);
                        lean_dec_ref_known(v___x_3132_, 1);
                        v___x_3134_ = 0;
                        v___x_3135_ = lean_box(0);
                        lean_inc(v_auxDeclName_3098_);
                        if v_isShared_3096_ == 0 {
                            lean_ctor_set(v___x_3095_, 2, v_a_3133_);
                            lean_ctor_set(v___x_3095_, 1, v___x_3135_);
                            lean_ctor_set(v___x_3095_, 0, v_auxDeclName_3098_);
                            v___x_3137_ = v___x_3095_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_3177_ = lean_alloc_ctor(3, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_auxDeclName_3098_);
                            lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3135_);
                            lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_a_3133_);
                            v___x_3137_ = v_reuseFailAlloc_3177_;
                            state = 15;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3095_);
                        lean_dec_ref_known(v_code_3015_, 2);
                        v_a_3178_ = lean_ctor_get(v___x_3132_, 0);
                        v_isSharedCheck_3185_ = (!lean_is_exclusive(v___x_3132_)) as u8;
                        if v_isSharedCheck_3185_ == 0 {
                            v___x_3180_ = v___x_3132_;
                            v_isShared_3181_ = v_isSharedCheck_3185_;
                            state = 24;
                            continue;
                        } else {
                            lean_inc(v_a_3178_);
                            lean_dec(v___x_3132_);
                            v___x_3180_ = lean_box(0);
                            v_isShared_3181_ = v_isSharedCheck_3185_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_3123_ = lean_ptr_addr(v_k_3091_);
                v___x_3124_ = lean_ptr_addr(v_a_3102_);
                v___x_3125_ = lean_usize_dec_eq(v___x_3123_, v___x_3124_);
                if v___x_3125_ == 0 {
                    v___y_3107_ = v___x_3125_;
                    state = 10;
                    continue;
                } else {
                    v___x_3126_ = lean_ptr_addr(v_decl_3089_);
                    v___x_3127_ = lean_usize_dec_eq(v___x_3126_, v___x_3126_);
                    v___y_3107_ = v___x_3127_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3107_ == 0 {
                    lean_inc_ref(v_decl_3089_);
                    v_isSharedCheck_3117_ = (!lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3117_ == 0 {
                        v_unused_3118_ = lean_ctor_get(v_code_3015_, 1);
                        lean_dec(v_unused_3118_);
                        v_unused_3119_ = lean_ctor_get(v_code_3015_, 0);
                        lean_dec(v_unused_3119_);
                        v___x_3109_ = v_code_3015_;
                        v_isShared_3110_ = v_isSharedCheck_3117_;
                        state = 11;
                        continue;
                    } else {
                        lean_dec(v_code_3015_);
                        v___x_3109_ = lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3117_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3102_);
                    if v_isShared_3105_ == 0 {
                        lean_ctor_set(v___x_3104_, 0, v_code_3015_);
                        v___x_3121_ = v___x_3104_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_code_3015_);
                        v___x_3121_ = v_reuseFailAlloc_3122_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_3110_ == 0 {
                    lean_ctor_set(v___x_3109_, 1, v_a_3102_);
                    v___x_3112_ = v___x_3109_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_decl_3089_);
                    lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_a_3102_);
                    v___x_3112_ = v_reuseFailAlloc_3116_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3105_ == 0 {
                    lean_ctor_set(v___x_3104_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3104_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3114_;
            }
            14 => {
                return v___x_3121_;
            }
            15 => {
                lean_inc_ref(v_decl_3089_);
                v___x_3138_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                    v___x_3134_,
                    v_decl_3089_,
                    v___x_3137_,
                    v_a_3018_,
                );
                if lean_obj_tag(v___x_3138_) == 0 {
                    v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
                    lean_inc(v_a_3139_);
                    lean_dec_ref_known(v___x_3138_, 1);
                    lean_inc_ref(v_k_3091_);
                    v___x_3140_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                        v_k_3091_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3140_) == 0 {
                        v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
                        v_isSharedCheck_3168_ = (!lean_is_exclusive(v___x_3140_)) as u8;
                        if v_isSharedCheck_3168_ == 0 {
                            v___x_3143_ = v___x_3140_;
                            v_isShared_3144_ = v_isSharedCheck_3168_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_3141_);
                            lean_dec(v___x_3140_);
                            v___x_3143_ = lean_box(0);
                            v_isShared_3144_ = v_isSharedCheck_3168_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3139_);
                        lean_dec_ref_known(v_code_3015_, 2);
                        return v___x_3140_;
                    }
                } else {
                    lean_dec_ref_known(v_code_3015_, 2);
                    v_a_3169_ = lean_ctor_get(v___x_3138_, 0);
                    v_isSharedCheck_3176_ = (!lean_is_exclusive(v___x_3138_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3171_ = v___x_3138_;
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_3169_);
                        lean_dec(v___x_3138_);
                        v___x_3171_ = lean_box(0);
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 22;
                        continue;
                    }
                }
            }
            16 => {
                v___x_3162_ = lean_ptr_addr(v_k_3091_);
                v___x_3163_ = lean_ptr_addr(v_a_3141_);
                v___x_3164_ = lean_usize_dec_eq(v___x_3162_, v___x_3163_);
                if v___x_3164_ == 0 {
                    v___y_3146_ = v___x_3164_;
                    state = 17;
                    continue;
                } else {
                    v___x_3165_ = lean_ptr_addr(v_decl_3089_);
                    v___x_3166_ = lean_ptr_addr(v_a_3139_);
                    v___x_3167_ = lean_usize_dec_eq(v___x_3165_, v___x_3166_);
                    v___y_3146_ = v___x_3167_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v___y_3146_ == 0 {
                    v_isSharedCheck_3156_ = (!lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3156_ == 0 {
                        v_unused_3157_ = lean_ctor_get(v_code_3015_, 1);
                        lean_dec(v_unused_3157_);
                        v_unused_3158_ = lean_ctor_get(v_code_3015_, 0);
                        lean_dec(v_unused_3158_);
                        v___x_3148_ = v_code_3015_;
                        v_isShared_3149_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    } else {
                        lean_dec(v_code_3015_);
                        v___x_3148_ = lean_box(0);
                        v_isShared_3149_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3141_);
                    lean_dec(v_a_3139_);
                    if v_isShared_3144_ == 0 {
                        lean_ctor_set(v___x_3143_, 0, v_code_3015_);
                        v___x_3160_ = v___x_3143_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_code_3015_);
                        v___x_3160_ = v_reuseFailAlloc_3161_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_3149_ == 0 {
                    lean_ctor_set(v___x_3148_, 1, v_a_3141_);
                    lean_ctor_set(v___x_3148_, 0, v_a_3139_);
                    v___x_3151_ = v___x_3148_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3139_);
                    lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_a_3141_);
                    v___x_3151_ = v_reuseFailAlloc_3155_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3144_ == 0 {
                    lean_ctor_set(v___x_3143_, 0, v___x_3151_);
                    v___x_3153_ = v___x_3143_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
                    v___x_3153_ = v_reuseFailAlloc_3154_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3153_;
            }
            21 => {
                return v___x_3160_;
            }
            22 => {
                if v_isShared_3172_ == 0 {
                    v___x_3174_ = v___x_3171_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3174_;
            }
            24 => {
                if v_isShared_3181_ == 0 {
                    v___x_3183_ = v___x_3180_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3183_;
            }
            26 => {
                v___x_3211_ = lean_ptr_addr(v_k_3188_);
                v___x_3212_ = lean_ptr_addr(v_a_3190_);
                v___x_3213_ = lean_usize_dec_eq(v___x_3211_, v___x_3212_);
                if v___x_3213_ == 0 {
                    v___y_3195_ = v___x_3213_;
                    state = 27;
                    continue;
                } else {
                    v___x_3214_ = lean_ptr_addr(v_decl_3089_);
                    v___x_3215_ = lean_usize_dec_eq(v___x_3214_, v___x_3214_);
                    v___y_3195_ = v___x_3215_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v___y_3195_ == 0 {
                    lean_inc_ref(v_decl_3089_);
                    v_isSharedCheck_3205_ = (!lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3205_ == 0 {
                        v_unused_3206_ = lean_ctor_get(v_code_3015_, 1);
                        lean_dec(v_unused_3206_);
                        v_unused_3207_ = lean_ctor_get(v_code_3015_, 0);
                        lean_dec(v_unused_3207_);
                        v___x_3197_ = v_code_3015_;
                        v_isShared_3198_ = v_isSharedCheck_3205_;
                        state = 28;
                        continue;
                    } else {
                        lean_dec(v_code_3015_);
                        v___x_3197_ = lean_box(0);
                        v_isShared_3198_ = v_isSharedCheck_3205_;
                        state = 28;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3190_);
                    if v_isShared_3193_ == 0 {
                        lean_ctor_set(v___x_3192_, 0, v_code_3015_);
                        v___x_3209_ = v___x_3192_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_code_3015_);
                        v___x_3209_ = v_reuseFailAlloc_3210_;
                        state = 31;
                        continue;
                    }
                }
            }
            28 => {
                if v_isShared_3198_ == 0 {
                    lean_ctor_set(v___x_3197_, 1, v_a_3190_);
                    v___x_3200_ = v___x_3197_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_decl_3089_);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_a_3190_);
                    v___x_3200_ = v_reuseFailAlloc_3204_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_3193_ == 0 {
                    lean_ctor_set(v___x_3192_, 0, v___x_3200_);
                    v___x_3202_ = v___x_3192_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
                    v___x_3202_ = v_reuseFailAlloc_3203_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3202_;
            }
            31 => {
                return v___x_3209_;
            }
            32 => {
                v___x_3229_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_3225_);
                v___x_3230_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_3229_, v_alts_3225_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
                if lean_obj_tag(v___x_3230_) == 0 {
                    v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
                    v_isSharedCheck_3255_ = (!lean_is_exclusive(v___x_3230_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v___x_3233_ = v___x_3230_;
                        v_isShared_3234_ = v_isSharedCheck_3255_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_3231_);
                        lean_dec(v___x_3230_);
                        v___x_3233_ = lean_box(0);
                        v_isShared_3234_ = v_isSharedCheck_3255_;
                        state = 33;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3227_);
                    lean_dec_ref(v_alts_3225_);
                    lean_dec(v_discr_3224_);
                    lean_dec_ref(v_resultType_3223_);
                    lean_dec(v_typeName_3222_);
                    lean_dec_ref_known(v_code_3015_, 1);
                    v_a_3256_ = lean_ctor_get(v___x_3230_, 0);
                    v_isSharedCheck_3263_ = (!lean_is_exclusive(v___x_3230_)) as u8;
                    if v_isSharedCheck_3263_ == 0 {
                        v___x_3258_ = v___x_3230_;
                        v_isShared_3259_ = v_isSharedCheck_3263_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_a_3256_);
                        lean_dec(v___x_3230_);
                        v___x_3258_ = lean_box(0);
                        v_isShared_3259_ = v_isSharedCheck_3263_;
                        state = 39;
                        continue;
                    }
                }
            }
            33 => {
                v___x_3235_ = lean_ptr_addr(v_alts_3225_);
                lean_dec_ref(v_alts_3225_);
                v___x_3236_ = lean_ptr_addr(v_a_3231_);
                v___x_3237_ = lean_usize_dec_eq(v___x_3235_, v___x_3236_);
                if v___x_3237_ == 0 {
                    v_isSharedCheck_3250_ = (!lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3250_ == 0 {
                        v_unused_3251_ = lean_ctor_get(v_code_3015_, 0);
                        lean_dec(v_unused_3251_);
                        v___x_3239_ = v_code_3015_;
                        v_isShared_3240_ = v_isSharedCheck_3250_;
                        state = 34;
                        continue;
                    } else {
                        lean_dec(v_code_3015_);
                        v___x_3239_ = lean_box(0);
                        v_isShared_3240_ = v_isSharedCheck_3250_;
                        state = 34;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3231_);
                    lean_del_object(v___x_3227_);
                    lean_dec(v_discr_3224_);
                    lean_dec_ref(v_resultType_3223_);
                    lean_dec(v_typeName_3222_);
                    if v_isShared_3234_ == 0 {
                        lean_ctor_set(v___x_3233_, 0, v_code_3015_);
                        v___x_3253_ = v___x_3233_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_code_3015_);
                        v___x_3253_ = v_reuseFailAlloc_3254_;
                        state = 38;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_3228_ == 0 {
                    lean_ctor_set(v___x_3227_, 3, v_a_3231_);
                    v___x_3242_ = v___x_3227_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_typeName_3222_);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_resultType_3223_);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_discr_3224_);
                    lean_ctor_set(v_reuseFailAlloc_3249_, 3, v_a_3231_);
                    v___x_3242_ = v_reuseFailAlloc_3249_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3240_ == 0 {
                    lean_ctor_set(v___x_3239_, 0, v___x_3242_);
                    v___x_3244_ = v___x_3239_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3242_);
                    v___x_3244_ = v_reuseFailAlloc_3248_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_3234_ == 0 {
                    lean_ctor_set(v___x_3233_, 0, v___x_3244_);
                    v___x_3246_ = v___x_3233_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
                    v___x_3246_ = v_reuseFailAlloc_3247_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3246_;
            }
            38 => {
                return v___x_3253_;
            }
            39 => {
                if v_isShared_3259_ == 0 {
                    v___x_3261_ = v___x_3258_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(
    mut v_i_3266_: *mut LeanObject,
    mut v_as_3267_: *mut LeanObject,
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
    mut v___y_3271_: *mut LeanObject,
    mut v___y_3272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: usize = 0;
    let mut v___x_3284_: usize = 0;
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut v_code_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3274_ = lean_array_get_size(v_as_3267_);
                v___x_3275_ = lean_nat_dec_lt(v_i_3266_, v___x_3274_);
                if v___x_3275_ == 0 {
                    lean_dec(v_i_3266_);
                    v___x_3276_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3276_, 0, v_as_3267_);
                    return v___x_3276_;
                } else {
                    v_a_3277_ = lean_array_fget_borrowed(v_as_3267_, v_i_3266_);
                    match lean_obj_tag(v_a_3277_) {
                        0 => {
                            v_code_3301_ = lean_ctor_get(v_a_3277_, 2);
                            lean_inc_ref(v_code_3301_);
                            v___y_3279_ = v_code_3301_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_3302_ = lean_ctor_get(v_a_3277_, 1);
                            lean_inc_ref(v_code_3302_);
                            v___y_3279_ = v_code_3302_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_3303_ = lean_ctor_get(v_a_3277_, 0);
                            lean_inc_ref(v_code_3303_);
                            v___y_3279_ = v_code_3303_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3280_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                    v___y_3279_,
                    v___y_3268_,
                    v___y_3269_,
                    v___y_3270_,
                    v___y_3271_,
                    v___y_3272_,
                );
                if lean_obj_tag(v___x_3280_) == 0 {
                    v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
                    lean_inc(v_a_3281_);
                    lean_dec_ref_known(v___x_3280_, 1);
                    lean_inc(v_a_3277_);
                    v___x_3282_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3277_, v_a_3281_);
                    v___x_3283_ = lean_ptr_addr(v_a_3277_);
                    v___x_3284_ = lean_ptr_addr(v___x_3282_);
                    v___x_3285_ = lean_usize_dec_eq(v___x_3283_, v___x_3284_);
                    if v___x_3285_ == 0 {
                        v___x_3286_ = lean_unsigned_to_nat(1);
                        v___x_3287_ = lean_nat_add(v_i_3266_, v___x_3286_);
                        v___x_3288_ = lean_array_fset(v_as_3267_, v_i_3266_, v___x_3282_);
                        lean_dec(v_i_3266_);
                        v_i_3266_ = v___x_3287_;
                        v_as_3267_ = v___x_3288_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___x_3282_);
                        v___x_3290_ = lean_unsigned_to_nat(1);
                        v___x_3291_ = lean_nat_add(v_i_3266_, v___x_3290_);
                        lean_dec(v_i_3266_);
                        v_i_3266_ = v___x_3291_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_as_3267_);
                    lean_dec(v_i_3266_);
                    v_a_3293_ = lean_ctor_get(v___x_3280_, 0);
                    v_isSharedCheck_3300_ = (!lean_is_exclusive(v___x_3280_)) as u8;
                    if v_isSharedCheck_3300_ == 0 {
                        v___x_3295_ = v___x_3280_;
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3293_);
                        lean_dec(v___x_3280_);
                        v___x_3295_ = lean_box(0);
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3296_ == 0 {
                    v___x_3298_ = v___x_3295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
                    v___x_3298_ = v_reuseFailAlloc_3299_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(
    mut v_i_3304_: *mut LeanObject,
    mut v_as_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3312_: *mut LeanObject = core::ptr::null_mut();
    v_res_3312_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_3304_, v_as_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
    lean_dec(v___y_3310_);
    lean_dec_ref(v___y_3309_);
    lean_dec(v___y_3308_);
    lean_dec_ref(v___y_3307_);
    lean_dec_ref(v___y_3306_);
    return v_res_3312_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(
    mut v_code_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
    mut v_a_3316_: *mut LeanObject,
    mut v_a_3317_: *mut LeanObject,
    mut v_a_3318_: *mut LeanObject,
    mut v_a_3319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3320_: *mut LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
        v_code_3313_,
        v_a_3314_,
        v_a_3315_,
        v_a_3316_,
        v_a_3317_,
        v_a_3318_,
    );
    lean_dec(v_a_3318_);
    lean_dec_ref(v_a_3317_);
    lean_dec(v_a_3316_);
    lean_dec_ref(v_a_3315_);
    lean_dec_ref(v_a_3314_);
    return v_res_3320_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(
    mut v_args_3321_: *mut LeanObject,
    mut v_upperBound_3322_: *mut LeanObject,
    mut v___x_3323_: *mut LeanObject,
    mut v_inst_3324_: *mut LeanObject,
    mut v_R_3325_: *mut LeanObject,
    mut v_a_3326_: *mut LeanObject,
    mut v_b_3327_: *mut LeanObject,
    mut v_c_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    v___x_3335_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_3321_, v_upperBound_3322_, v___x_3323_, v_a_3326_, v_b_3327_);
    return v___x_3335_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(
    mut v_args_3336_: *mut LeanObject,
    mut v_upperBound_3337_: *mut LeanObject,
    mut v___x_3338_: *mut LeanObject,
    mut v_inst_3339_: *mut LeanObject,
    mut v_R_3340_: *mut LeanObject,
    mut v_a_3341_: *mut LeanObject,
    mut v_b_3342_: *mut LeanObject,
    mut v_c_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3350_: *mut LeanObject = core::ptr::null_mut();
    v_res_3350_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(
            v_args_3336_,
            v_upperBound_3337_,
            v___x_3338_,
            v_inst_3339_,
            v_R_3340_,
            v_a_3341_,
            v_b_3342_,
            v_c_3343_,
            v___y_3344_,
            v___y_3345_,
            v___y_3346_,
            v___y_3347_,
            v___y_3348_,
        );
    lean_dec(v___y_3348_);
    lean_dec_ref(v___y_3347_);
    lean_dec(v___y_3346_);
    lean_dec_ref(v___y_3345_);
    lean_dec_ref(v___y_3344_);
    lean_dec_ref(v___x_3338_);
    lean_dec(v_upperBound_3337_);
    lean_dec_ref(v_args_3336_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(
    mut v_f_3351_: *mut LeanObject,
    mut v_v_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v_a_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3382_: u8 = 0;
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_3352_) == 0 {
                    v_code_3359_ = lean_ctor_get(v_v_3352_, 0);
                    v_isSharedCheck_3383_ = (!lean_is_exclusive(v_v_3352_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v___x_3361_ = v_v_3352_;
                        v_isShared_3362_ = v_isSharedCheck_3383_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_3359_);
                        lean_dec(v_v_3352_);
                        v___x_3361_ = lean_box(0);
                        v_isShared_3362_ = v_isSharedCheck_3383_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_3351_);
                    v___x_3384_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3384_, 0, v_v_3352_);
                    return v___x_3384_;
                }
            }
            1 => {
                lean_inc(v___y_3357_);
                lean_inc_ref(v___y_3356_);
                lean_inc(v___y_3355_);
                lean_inc_ref(v___y_3354_);
                lean_inc_ref(v___y_3353_);
                v___x_3363_ = lean_apply_7(
                    v_f_3351_,
                    v_code_3359_,
                    v___y_3353_,
                    v___y_3354_,
                    v___y_3355_,
                    v___y_3356_,
                    v___y_3357_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3363_) == 0 {
                    v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
                    v_isSharedCheck_3374_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3374_ == 0 {
                        v___x_3366_ = v___x_3363_;
                        v_isShared_3367_ = v_isSharedCheck_3374_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3364_);
                        lean_dec(v___x_3363_);
                        v___x_3366_ = lean_box(0);
                        v_isShared_3367_ = v_isSharedCheck_3374_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3361_);
                    v_a_3375_ = lean_ctor_get(v___x_3363_, 0);
                    v_isSharedCheck_3382_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3382_ == 0 {
                        v___x_3377_ = v___x_3363_;
                        v_isShared_3378_ = v_isSharedCheck_3382_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3375_);
                        lean_dec(v___x_3363_);
                        v___x_3377_ = lean_box(0);
                        v_isShared_3378_ = v_isSharedCheck_3382_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3362_ == 0 {
                    lean_ctor_set(v___x_3361_, 0, v_a_3364_);
                    v___x_3369_ = v___x_3361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3364_);
                    v___x_3369_ = v_reuseFailAlloc_3373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3367_ == 0 {
                    lean_ctor_set(v___x_3366_, 0, v___x_3369_);
                    v___x_3371_ = v___x_3366_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
                    v___x_3371_ = v_reuseFailAlloc_3372_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3371_;
            }
            5 => {
                if v_isShared_3378_ == 0 {
                    v___x_3380_ = v___x_3377_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
                    v___x_3380_ = v_reuseFailAlloc_3381_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(
    mut v_f_3385_: *mut LeanObject,
    mut v_v_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3393_: *mut LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_3385_, v_v_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    lean_dec(v___y_3391_);
    lean_dec_ref(v___y_3390_);
    lean_dec(v___y_3389_);
    lean_dec_ref(v___y_3388_);
    lean_dec_ref(v___y_3387_);
    return v_res_3393_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(
    mut v_pu_3394_: u8,
    mut v_f_3395_: *mut LeanObject,
    mut v_v_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    v___x_3403_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_3395_, v_v_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
    return v___x_3403_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(
    mut v_pu_3404_: *mut LeanObject,
    mut v_f_3405_: *mut LeanObject,
    mut v_v_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_3413_: u8 = 0;
    let mut v_res_3414_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_3413_ = (lean_unbox(v_pu_3404_) as u8);
    v_res_3414_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_3413_, v_f_3405_, v_v_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
    lean_dec(v___y_3411_);
    lean_dec_ref(v___y_3410_);
    lean_dec(v___y_3409_);
    lean_dec_ref(v___y_3408_);
    lean_dec_ref(v___y_3407_);
    return v_res_3414_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0()
-> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3415_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1()
-> *mut LeanObject {
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3416_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0,
    );
    v___x_3417_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3417_, 0, v___x_3416_);
    return v___x_3417_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2()
-> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1,
    );
    v___x_3419_ = lean_unsigned_to_nat(0);
    v___x_3420_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3420_, 0, v___x_3419_);
    lean_ctor_set(v___x_3420_, 1, v___x_3419_);
    lean_ctor_set(v___x_3420_, 2, v___x_3419_);
    lean_ctor_set(v___x_3420_, 3, v___x_3419_);
    lean_ctor_set(v___x_3420_, 4, v___x_3418_);
    lean_ctor_set(v___x_3420_, 5, v___x_3418_);
    lean_ctor_set(v___x_3420_, 6, v___x_3418_);
    lean_ctor_set(v___x_3420_, 7, v___x_3418_);
    lean_ctor_set(v___x_3420_, 8, v___x_3418_);
    lean_ctor_set(v___x_3420_, 9, v___x_3418_);
    return v___x_3420_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3()
-> f64 {
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: f64 = 0.0;
    v___x_3421_ = lean_unsigned_to_nat(0);
    v___x_3422_ = lean_float_of_nat(v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(
    mut v_cls_3426_: *mut LeanObject,
    mut v_msg_3427_: *mut LeanObject,
    mut v___y_3428_: *mut LeanObject,
    mut v___y_3429_: *mut LeanObject,
    mut v___y_3430_: *mut LeanObject,
    mut v___y_3431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v_env_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3446_: u8 = 0;
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v_tid_3461_: u64 = 0;
    let mut v_traces_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: u8 = 0;
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: f64 = 0.0;
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut v_unused_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut v_a_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3433_ = lean_ctor_get(v___y_3430_, 2);
                v_ref_3434_ = lean_ctor_get(v___y_3430_, 5);
                v___x_3435_ = lean_st_ref_get(v___y_3431_);
                v___x_3436_ = lean_st_ref_get(v___y_3429_);
                v___x_3437_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3428_);
                if lean_obj_tag(v___x_3437_) == 0 {
                    v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
                    v_isSharedCheck_3496_ = (!lean_is_exclusive(v___x_3437_)) as u8;
                    if v_isSharedCheck_3496_ == 0 {
                        v___x_3440_ = v___x_3437_;
                        v_isShared_3441_ = v_isSharedCheck_3496_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3438_);
                        lean_dec(v___x_3437_);
                        v___x_3440_ = lean_box(0);
                        v_isShared_3441_ = v_isSharedCheck_3496_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3436_);
                    lean_dec(v___x_3435_);
                    lean_dec_ref(v_msg_3427_);
                    lean_dec(v_cls_3426_);
                    v_a_3497_ = lean_ctor_get(v___x_3437_, 0);
                    v_isSharedCheck_3504_ = (!lean_is_exclusive(v___x_3437_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3499_ = v___x_3437_;
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3497_);
                        lean_dec(v___x_3437_);
                        v___x_3499_ = lean_box(0);
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3442_ = lean_ctor_get(v___x_3435_, 0);
                lean_inc_ref(v_env_3442_);
                lean_dec(v___x_3435_);
                v_lctx_3443_ = lean_ctor_get(v___x_3436_, 0);
                v_isSharedCheck_3494_ = (!lean_is_exclusive(v___x_3436_)) as u8;
                if v_isSharedCheck_3494_ == 0 {
                    v_unused_3495_ = lean_ctor_get(v___x_3436_, 1);
                    lean_dec(v_unused_3495_);
                    v___x_3445_ = v___x_3436_;
                    v_isShared_3446_ = v_isSharedCheck_3494_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_3443_);
                    lean_dec(v___x_3436_);
                    v___x_3445_ = lean_box(0);
                    v_isShared_3446_ = v_isSharedCheck_3494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3447_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
                v___x_3448_ = lean_st_ref_take(v___y_3431_);
                v_traceState_3449_ = lean_ctor_get(v___x_3448_, 4);
                v_env_3450_ = lean_ctor_get(v___x_3448_, 0);
                v_nextMacroScope_3451_ = lean_ctor_get(v___x_3448_, 1);
                v_ngen_3452_ = lean_ctor_get(v___x_3448_, 2);
                v_auxDeclNGen_3453_ = lean_ctor_get(v___x_3448_, 3);
                v_cache_3454_ = lean_ctor_get(v___x_3448_, 5);
                v_messages_3455_ = lean_ctor_get(v___x_3448_, 6);
                v_infoState_3456_ = lean_ctor_get(v___x_3448_, 7);
                v_snapshotTasks_3457_ = lean_ctor_get(v___x_3448_, 8);
                v_isSharedCheck_3493_ = (!lean_is_exclusive(v___x_3448_)) as u8;
                if v_isSharedCheck_3493_ == 0 {
                    v___x_3459_ = v___x_3448_;
                    v_isShared_3460_ = v_isSharedCheck_3493_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3457_);
                    lean_inc(v_infoState_3456_);
                    lean_inc(v_messages_3455_);
                    lean_inc(v_cache_3454_);
                    lean_inc(v_traceState_3449_);
                    lean_inc(v_auxDeclNGen_3453_);
                    lean_inc(v_ngen_3452_);
                    lean_inc(v_nextMacroScope_3451_);
                    lean_inc(v_env_3450_);
                    lean_dec(v___x_3448_);
                    v___x_3459_ = lean_box(0);
                    v_isShared_3460_ = v_isSharedCheck_3493_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_3461_ = lean_ctor_get_uint64(
                    v_traceState_3449_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3462_ = lean_ctor_get(v_traceState_3449_, 0);
                v_isSharedCheck_3492_ = (!lean_is_exclusive(v_traceState_3449_)) as u8;
                if v_isSharedCheck_3492_ == 0 {
                    v___x_3464_ = v_traceState_3449_;
                    v_isShared_3465_ = v_isSharedCheck_3492_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_traces_3462_);
                    lean_dec(v_traceState_3449_);
                    v___x_3464_ = lean_box(0);
                    v_isShared_3465_ = v_isSharedCheck_3492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3466_ = (lean_unbox(v_a_3438_) as u8);
                lean_dec(v_a_3438_);
                v___x_3467_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3443_, v___x_3466_);
                lean_dec_ref(v_lctx_3443_);
                lean_inc_ref(v_options_3433_);
                v___x_3468_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3468_, 0, v_env_3442_);
                lean_ctor_set(v___x_3468_, 1, v___x_3447_);
                lean_ctor_set(v___x_3468_, 2, v___x_3467_);
                lean_ctor_set(v___x_3468_, 3, v_options_3433_);
                if v_isShared_3446_ == 0 {
                    lean_ctor_set_tag(v___x_3445_, 3);
                    lean_ctor_set(v___x_3445_, 1, v_msg_3427_);
                    lean_ctor_set(v___x_3445_, 0, v___x_3468_);
                    v___x_3470_ = v___x_3445_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3468_);
                    lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_msg_3427_);
                    v___x_3470_ = v_reuseFailAlloc_3491_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3471_ = lean_box(0);
                v___x_3472_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
                v___x_3473_ = 0;
                v___x_3474_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4;
                v___x_3475_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3475_, 0, v_cls_3426_);
                lean_ctor_set(v___x_3475_, 1, v___x_3471_);
                lean_ctor_set(v___x_3475_, 2, v___x_3474_);
                lean_ctor_set_float(
                    v___x_3475_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3472_,
                );
                lean_ctor_set_float(
                    v___x_3475_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3472_,
                );
                lean_ctor_set_uint8(
                    v___x_3475_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3473_,
                );
                v___x_3476_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5;
                v___x_3477_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3477_, 0, v___x_3475_);
                lean_ctor_set(v___x_3477_, 1, v___x_3470_);
                lean_ctor_set(v___x_3477_, 2, v___x_3476_);
                lean_inc(v_ref_3434_);
                v___x_3478_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3478_, 0, v_ref_3434_);
                lean_ctor_set(v___x_3478_, 1, v___x_3477_);
                v___x_3479_ = l_Lean_PersistentArray_push___redArg(v_traces_3462_, v___x_3478_);
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 0, v___x_3479_);
                    v___x_3481_ = v___x_3464_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3479_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3490_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3461_,
                    );
                    v___x_3481_ = v_reuseFailAlloc_3490_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3460_ == 0 {
                    lean_ctor_set(v___x_3459_, 4, v___x_3481_);
                    v___x_3483_ = v___x_3459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_env_3450_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_nextMacroScope_3451_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_ngen_3452_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_auxDeclNGen_3453_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 4, v___x_3481_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 5, v_cache_3454_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 6, v_messages_3455_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 7, v_infoState_3456_);
                    lean_ctor_set(v_reuseFailAlloc_3489_, 8, v_snapshotTasks_3457_);
                    v___x_3483_ = v_reuseFailAlloc_3489_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3484_ = lean_st_ref_set(v___y_3431_, v___x_3483_);
                v___x_3485_ = lean_box(0);
                if v_isShared_3441_ == 0 {
                    lean_ctor_set(v___x_3440_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3440_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3487_;
            }
            9 => {
                if v_isShared_3500_ == 0 {
                    v___x_3502_ = v___x_3499_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
                    v___x_3502_ = v_reuseFailAlloc_3503_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(
    mut v_cls_3505_: *mut LeanObject,
    mut v_msg_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3512_: *mut LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(
        v_cls_3505_,
        v_msg_3506_,
        v___y_3507_,
        v___y_3508_,
        v___y_3509_,
        v___y_3510_,
    );
    lean_dec(v___y_3510_);
    lean_dec_ref(v___y_3509_);
    lean_dec(v___y_3508_);
    lean_dec_ref(v___y_3507_);
    return v_res_3512_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(
    mut v_x_3513_: *mut LeanObject,
    mut v_x_3514_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3514_) == 0 {
        lean_inc(v_x_3513_);
        return v_x_3513_;
    } else {
        let mut v_key_3515_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_3516_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
        v_key_3515_ = lean_ctor_get(v_x_3514_, 0);
        v_tail_3516_ = lean_ctor_get(v_x_3514_, 2);
        v___x_3517_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_3513_, v_tail_3516_);
        lean_inc(v_key_3515_);
        v___x_3518_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3518_, 0, v_key_3515_);
        lean_ctor_set(v___x_3518_, 1, v___x_3517_);
        return v___x_3518_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(
    mut v_x_3519_: *mut LeanObject,
    mut v_x_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3521_: *mut LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_3519_, v_x_3520_);
    lean_dec(v_x_3520_);
    lean_dec(v_x_3519_);
    return v_res_3521_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(
    mut v_as_3522_: *mut LeanObject,
    mut v_i_3523_: usize,
    mut v_stop_3524_: usize,
    mut v_b_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3526_: u8 = 0;
    let mut v___x_3527_: usize = 0;
    let mut v___x_3528_: usize = 0;
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3526_ = lean_usize_dec_eq(v_i_3523_, v_stop_3524_);
                if v___x_3526_ == 0 {
                    v___x_3527_ = 1usize;
                    v___x_3528_ = lean_usize_sub(v_i_3523_, v___x_3527_);
                    v___x_3529_ = lean_array_uget_borrowed(v_as_3522_, v___x_3528_);
                    v___x_3530_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_3525_, v___x_3529_);
                    lean_dec(v_b_3525_);
                    v_i_3523_ = v___x_3528_;
                    v_b_3525_ = v___x_3530_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3525_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(
    mut v_as_3532_: *mut LeanObject,
    mut v_i_3533_: *mut LeanObject,
    mut v_stop_3534_: *mut LeanObject,
    mut v_b_3535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3536_: usize = 0;
    let mut v_stop_boxed_3537_: usize = 0;
    let mut v_res_3538_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3536_ = lean_unbox_usize(v_i_3533_);
    lean_dec(v_i_3533_);
    v_stop_boxed_3537_ = lean_unbox_usize(v_stop_3534_);
    lean_dec(v_stop_3534_);
    v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_3532_, v_i_boxed_3536_, v_stop_boxed_3537_, v_b_3535_);
    lean_dec_ref(v_as_3532_);
    return v_res_3538_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(
    mut v_m_3539_: *mut LeanObject,
    mut v_a_3540_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u64 = 0;
    let mut v___x_3544_: u64 = 0;
    let mut v___x_3545_: u64 = 0;
    let mut v_fold_3546_: u64 = 0;
    let mut v___x_3547_: u64 = 0;
    let mut v___x_3548_: u64 = 0;
    let mut v___x_3549_: u64 = 0;
    let mut v___x_3550_: usize = 0;
    let mut v___x_3551_: usize = 0;
    let mut v___x_3552_: usize = 0;
    let mut v___x_3553_: usize = 0;
    let mut v___x_3554_: usize = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    v_buckets_3541_ = lean_ctor_get(v_m_3539_, 1);
    v___x_3542_ = lean_array_get_size(v_buckets_3541_);
    v___x_3543_ = l_Lean_instHashableFVarId_hash(v_a_3540_);
    v___x_3544_ = 32u64;
    v___x_3545_ = lean_uint64_shift_right(v___x_3543_, v___x_3544_);
    v_fold_3546_ = lean_uint64_xor(v___x_3543_, v___x_3545_);
    v___x_3547_ = 16u64;
    v___x_3548_ = lean_uint64_shift_right(v_fold_3546_, v___x_3547_);
    v___x_3549_ = lean_uint64_xor(v_fold_3546_, v___x_3548_);
    v___x_3550_ = lean_uint64_to_usize(v___x_3549_);
    v___x_3551_ = lean_usize_of_nat(v___x_3542_);
    v___x_3552_ = 1usize;
    v___x_3553_ = lean_usize_sub(v___x_3551_, v___x_3552_);
    v___x_3554_ = lean_usize_land(v___x_3550_, v___x_3553_);
    v___x_3555_ = lean_array_uget_borrowed(v_buckets_3541_, v___x_3554_);
    v___x_3556_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_3540_, v___x_3555_);
    return v___x_3556_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(
    mut v_m_3557_: *mut LeanObject,
    mut v_a_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_3557_, v_a_3558_);
    lean_dec(v_a_3558_);
    lean_dec_ref(v_m_3557_);
    v_r_3560_ = lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(
    mut v_a_3561_: *mut LeanObject,
    mut v_as_3562_: *mut LeanObject,
    mut v_i_3563_: usize,
    mut v_stop_3564_: usize,
    mut v_b_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: usize = 0;
    let mut v___x_3569_: usize = 0;
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3571_ = lean_usize_dec_eq(v_i_3563_, v_stop_3564_);
                if v___x_3571_ == 0 {
                    v___x_3572_ = lean_array_uget_borrowed(v_as_3562_, v_i_3563_);
                    v_fvarId_3573_ = lean_ctor_get(v___x_3572_, 0);
                    v___x_3574_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3561_, v_fvarId_3573_);
                    if v___x_3574_ == 0 {
                        v___y_3567_ = v_b_3565_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_3572_);
                        v___x_3575_ = lean_array_push(v_b_3565_, v___x_3572_);
                        v___y_3567_ = v___x_3575_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3565_;
                }
            }
            1 => {
                v___x_3568_ = 1usize;
                v___x_3569_ = lean_usize_add(v_i_3563_, v___x_3568_);
                v_i_3563_ = v___x_3569_;
                v_b_3565_ = v___y_3567_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7___boxed(
    mut v_a_3576_: *mut LeanObject,
    mut v_as_3577_: *mut LeanObject,
    mut v_i_3578_: *mut LeanObject,
    mut v_stop_3579_: *mut LeanObject,
    mut v_b_3580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3581_: usize = 0;
    let mut v_stop_boxed_3582_: usize = 0;
    let mut v_res_3583_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3581_ = lean_unbox_usize(v_i_3578_);
    lean_dec(v_i_3578_);
    v_stop_boxed_3582_ = lean_unbox_usize(v_stop_3579_);
    lean_dec(v_stop_3579_);
    v_res_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_3576_, v_as_3577_, v_i_boxed_3581_, v_stop_boxed_3582_, v_b_3580_);
    lean_dec_ref(v_as_3577_);
    lean_dec_ref(v_a_3576_);
    return v_res_3583_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(
    mut v_a_3584_: *mut LeanObject,
    mut v_as_3585_: *mut LeanObject,
    mut v_i_3586_: usize,
    mut v_stop_3587_: usize,
    mut v_b_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: usize = 0;
    let mut v___x_3592_: usize = 0;
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3594_ = lean_usize_dec_eq(v_i_3586_, v_stop_3587_);
                if v___x_3594_ == 0 {
                    v___x_3595_ = lean_array_uget_borrowed(v_as_3585_, v_i_3586_);
                    v_fvarId_3596_ = lean_ctor_get(v___x_3595_, 0);
                    v___x_3597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3584_, v_fvarId_3596_);
                    if v___x_3597_ == 0 {
                        v___y_3590_ = v_b_3588_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v___x_3595_);
                        v___x_3598_ = lean_array_push(v_b_3588_, v___x_3595_);
                        v___y_3590_ = v___x_3598_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3588_;
                }
            }
            1 => {
                v___x_3591_ = 1usize;
                v___x_3592_ = lean_usize_add(v_i_3586_, v___x_3591_);
                v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_3584_, v_as_3585_, v___x_3592_, v_stop_3587_, v___y_3590_);
                return v___x_3593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(
    mut v_a_3599_: *mut LeanObject,
    mut v_as_3600_: *mut LeanObject,
    mut v_i_3601_: *mut LeanObject,
    mut v_stop_3602_: *mut LeanObject,
    mut v_b_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3604_: usize = 0;
    let mut v_stop_boxed_3605_: usize = 0;
    let mut v_res_3606_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3604_ = lean_unbox_usize(v_i_3601_);
    lean_dec(v_i_3601_);
    v_stop_boxed_3605_ = lean_unbox_usize(v_stop_3602_);
    lean_dec(v_stop_3602_);
    v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_3599_, v_as_3600_, v_i_boxed_3604_, v_stop_boxed_3605_, v_b_3603_);
    lean_dec_ref(v_as_3600_);
    lean_dec_ref(v_a_3599_);
    return v_res_3606_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3607_) == 0 {
                    v___x_3609_ = l_List_reverse___redArg(v_a_3608_);
                    return v___x_3609_;
                } else {
                    v_head_3610_ = lean_ctor_get(v_a_3607_, 0);
                    v_tail_3611_ = lean_ctor_get(v_a_3607_, 1);
                    v_isSharedCheck_3620_ = (!lean_is_exclusive(v_a_3607_)) as u8;
                    if v_isSharedCheck_3620_ == 0 {
                        v___x_3613_ = v_a_3607_;
                        v_isShared_3614_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3611_);
                        lean_inc(v_head_3610_);
                        lean_dec(v_a_3607_);
                        v___x_3613_ = lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3615_ = l_Lean_MessageData_ofExpr(v_head_3610_);
                if v_isShared_3614_ == 0 {
                    lean_ctor_set(v___x_3613_, 1, v_a_3608_);
                    lean_ctor_set(v___x_3613_, 0, v___x_3615_);
                    v___x_3617_ = v___x_3613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3615_);
                    lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_a_3608_);
                    v___x_3617_ = v_reuseFailAlloc_3619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3607_ = v_tail_3611_;
                v_a_3608_ = v___x_3617_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(
    mut v_as_3621_: *mut LeanObject,
    mut v_sz_3622_: usize,
    mut v_i_3623_: usize,
    mut v_b_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: usize = 0;
    let mut v___x_3629_: usize = 0;
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v_array_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v_a_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: u8 = 0;
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_unused_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3631_ = lean_usize_dec_lt(v_i_3623_, v_sz_3622_);
                if v___x_3631_ == 0 {
                    v___x_3632_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3632_, 0, v_b_3624_);
                    return v___x_3632_;
                } else {
                    v_snd_3633_ = lean_ctor_get(v_b_3624_, 1);
                    v_fst_3634_ = lean_ctor_get(v_b_3624_, 0);
                    v_isSharedCheck_3669_ = (!lean_is_exclusive(v_b_3624_)) as u8;
                    if v_isSharedCheck_3669_ == 0 {
                        v___x_3636_ = v_b_3624_;
                        v_isShared_3637_ = v_isSharedCheck_3669_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3633_);
                        lean_inc(v_fst_3634_);
                        lean_dec(v_b_3624_);
                        v___x_3636_ = lean_box(0);
                        v_isShared_3637_ = v_isSharedCheck_3669_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3628_ = 1usize;
                v___x_3629_ = lean_usize_add(v_i_3623_, v___x_3628_);
                v_i_3623_ = v___x_3629_;
                v_b_3624_ = v_a_3627_;
                state = 0;
                continue;
            }
            2 => {
                v_array_3638_ = lean_ctor_get(v_snd_3633_, 0);
                v_start_3639_ = lean_ctor_get(v_snd_3633_, 1);
                v_stop_3640_ = lean_ctor_get(v_snd_3633_, 2);
                v___x_3641_ = lean_nat_dec_lt(v_start_3639_, v_stop_3640_);
                if v___x_3641_ == 0 {
                    if v_isShared_3637_ == 0 {
                        v___x_3643_ = v___x_3636_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_fst_3634_);
                        lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_snd_3633_);
                        v___x_3643_ = v_reuseFailAlloc_3645_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_3640_);
                    lean_inc(v_start_3639_);
                    lean_inc_ref(v_array_3638_);
                    v_isSharedCheck_3665_ = (!lean_is_exclusive(v_snd_3633_)) as u8;
                    if v_isSharedCheck_3665_ == 0 {
                        v_unused_3666_ = lean_ctor_get(v_snd_3633_, 2);
                        lean_dec(v_unused_3666_);
                        v_unused_3667_ = lean_ctor_get(v_snd_3633_, 1);
                        lean_dec(v_unused_3667_);
                        v_unused_3668_ = lean_ctor_get(v_snd_3633_, 0);
                        lean_dec(v_unused_3668_);
                        v___x_3647_ = v_snd_3633_;
                        v_isShared_3648_ = v_isSharedCheck_3665_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_snd_3633_);
                        v___x_3647_ = lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3665_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3644_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                return v___x_3644_;
            }
            4 => {
                v_a_3649_ = lean_array_uget_borrowed(v_as_3621_, v_i_3623_);
                v___x_3650_ = lean_array_fget(v_array_3638_, v_start_3639_);
                v___x_3651_ = lean_unsigned_to_nat(1);
                v___x_3652_ = lean_nat_add(v_start_3639_, v___x_3651_);
                lean_dec(v_start_3639_);
                if v_isShared_3648_ == 0 {
                    lean_ctor_set(v___x_3647_, 1, v___x_3652_);
                    v___x_3654_ = v___x_3647_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_array_3638_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___x_3652_);
                    lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_stop_3640_);
                    v___x_3654_ = v_reuseFailAlloc_3664_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3655_ = (lean_unbox(v_a_3649_) as u8);
                if v___x_3655_ == 0 {
                    lean_dec(v___x_3650_);
                    if v_isShared_3637_ == 0 {
                        lean_ctor_set(v___x_3636_, 1, v___x_3654_);
                        v___x_3657_ = v___x_3636_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_fst_3634_);
                        lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3654_);
                        v___x_3657_ = v_reuseFailAlloc_3658_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_3659_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_3650_);
                    lean_dec(v___x_3650_);
                    v___x_3660_ = lean_array_push(v_fst_3634_, v___x_3659_);
                    if v_isShared_3637_ == 0 {
                        lean_ctor_set(v___x_3636_, 1, v___x_3654_);
                        lean_ctor_set(v___x_3636_, 0, v___x_3660_);
                        v___x_3662_ = v___x_3636_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3660_);
                        lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___x_3654_);
                        v___x_3662_ = v_reuseFailAlloc_3663_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v_a_3627_ = v___x_3657_;
                state = 1;
                continue;
            }
            7 => {
                v_a_3627_ = v___x_3662_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(
    mut v_as_3670_: *mut LeanObject,
    mut v_sz_3671_: *mut LeanObject,
    mut v_i_3672_: *mut LeanObject,
    mut v_b_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3675_: usize = 0;
    let mut v_i_boxed_3676_: usize = 0;
    let mut v_res_3677_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3675_ = lean_unbox_usize(v_sz_3671_);
    lean_dec(v_sz_3671_);
    v_i_boxed_3676_ = lean_unbox_usize(v_i_3672_);
    lean_dec(v_i_3672_);
    v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_3670_, v_sz_boxed_3675_, v_i_boxed_3676_, v_b_3673_);
    lean_dec_ref(v_as_3670_);
    return v_res_3677_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(
    mut v_sz_3678_: usize,
    mut v_i_3679_: usize,
    mut v_bs_3680_: *mut LeanObject,
    mut v___y_3681_: u8,
    mut v___y_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v_v_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: usize = 0;
    let mut v___x_3697_: usize = 0;
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3688_ = lean_usize_dec_lt(v_i_3679_, v_sz_3678_);
                if v___x_3688_ == 0 {
                    v___x_3689_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3689_, 0, v_bs_3680_);
                    return v___x_3689_;
                } else {
                    v___x_3690_ = 0;
                    v_v_3691_ = lean_array_uget_borrowed(v_bs_3680_, v_i_3679_);
                    lean_inc(v_v_3691_);
                    v___x_3692_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
                        v___x_3690_,
                        v_v_3691_,
                        v___y_3681_,
                        v___y_3682_,
                        v___y_3683_,
                        v___y_3684_,
                        v___y_3685_,
                        v___y_3686_,
                    );
                    if lean_obj_tag(v___x_3692_) == 0 {
                        v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
                        lean_inc(v_a_3693_);
                        lean_dec_ref_known(v___x_3692_, 1);
                        v___x_3694_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3695_ = lean_array_uset(v_bs_3680_, v_i_3679_, v___x_3694_);
                        v___x_3696_ = 1usize;
                        v___x_3697_ = lean_usize_add(v_i_3679_, v___x_3696_);
                        v___x_3698_ = lean_array_uset(v_bs_x27_3695_, v_i_3679_, v_a_3693_);
                        v_i_3679_ = v___x_3697_;
                        v_bs_3680_ = v___x_3698_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3680_);
                        v_a_3700_ = lean_ctor_get(v___x_3692_, 0);
                        v_isSharedCheck_3707_ = (!lean_is_exclusive(v___x_3692_)) as u8;
                        if v_isSharedCheck_3707_ == 0 {
                            v___x_3702_ = v___x_3692_;
                            v_isShared_3703_ = v_isSharedCheck_3707_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3700_);
                            lean_dec(v___x_3692_);
                            v___x_3702_ = lean_box(0);
                            v_isShared_3703_ = v_isSharedCheck_3707_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3703_ == 0 {
                    v___x_3705_ = v___x_3702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
                    v___x_3705_ = v_reuseFailAlloc_3706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(
    mut v_sz_3708_: *mut LeanObject,
    mut v_i_3709_: *mut LeanObject,
    mut v_bs_3710_: *mut LeanObject,
    mut v___y_3711_: *mut LeanObject,
    mut v___y_3712_: *mut LeanObject,
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
    mut v___y_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3718_: usize = 0;
    let mut v_i_boxed_3719_: usize = 0;
    let mut v___y_12534__boxed_3720_: u8 = 0;
    let mut v_res_3721_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3718_ = lean_unbox_usize(v_sz_3708_);
    lean_dec(v_sz_3708_);
    v_i_boxed_3719_ = lean_unbox_usize(v_i_3709_);
    lean_dec(v_i_3709_);
    v___y_12534__boxed_3720_ = (lean_unbox(v___y_3711_) as u8);
    v_res_3721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_3718_, v_i_boxed_3719_, v_bs_3710_, v___y_12534__boxed_3720_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
    lean_dec(v___y_3716_);
    lean_dec_ref(v___y_3715_);
    lean_dec(v___y_3714_);
    lean_dec_ref(v___y_3713_);
    lean_dec(v___y_3712_);
    return v_res_3721_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(
    mut v_a_3722_: *mut LeanObject,
    mut v_a_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3722_) == 0 {
                    v___x_3724_ = l_List_reverse___redArg(v_a_3723_);
                    return v___x_3724_;
                } else {
                    v_head_3725_ = lean_ctor_get(v_a_3722_, 0);
                    v_tail_3726_ = lean_ctor_get(v_a_3722_, 1);
                    v_isSharedCheck_3735_ = (!lean_is_exclusive(v_a_3722_)) as u8;
                    if v_isSharedCheck_3735_ == 0 {
                        v___x_3728_ = v_a_3722_;
                        v_isShared_3729_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3726_);
                        lean_inc(v_head_3725_);
                        lean_dec(v_a_3722_);
                        v___x_3728_ = lean_box(0);
                        v_isShared_3729_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3730_ = l_Lean_mkFVar(v_head_3725_);
                if v_isShared_3729_ == 0 {
                    lean_ctor_set(v___x_3728_, 1, v_a_3723_);
                    lean_ctor_set(v___x_3728_, 0, v___x_3730_);
                    v___x_3732_ = v___x_3728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3730_);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_a_3723_);
                    v___x_3732_ = v_reuseFailAlloc_3734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3722_ = v_tail_3726_;
                v_a_3723_ = v___x_3732_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(
    mut v_a_3736_: *mut LeanObject,
    mut v_sz_3737_: usize,
    mut v_i_3738_: usize,
    mut v_bs_3739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3740_: u8 = 0;
    let mut v_v_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: usize = 0;
    let mut v___x_3747_: usize = 0;
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3740_ = lean_usize_dec_lt(v_i_3738_, v_sz_3737_);
                if v___x_3740_ == 0 {
                    return v_bs_3739_;
                } else {
                    v_v_3741_ = lean_array_uget_borrowed(v_bs_3739_, v_i_3738_);
                    v_fvarId_3742_ = lean_ctor_get(v_v_3741_, 0);
                    lean_inc(v_fvarId_3742_);
                    v___x_3743_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3744_ = lean_array_uset(v_bs_3739_, v_i_3738_, v___x_3743_);
                    v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3736_, v_fvarId_3742_);
                    lean_dec(v_fvarId_3742_);
                    v___x_3746_ = 1usize;
                    v___x_3747_ = lean_usize_add(v_i_3738_, v___x_3746_);
                    v___x_3748_ = lean_box((v___x_3745_) as usize);
                    v___x_3749_ = lean_array_uset(v_bs_x27_3744_, v_i_3738_, v___x_3748_);
                    v_i_3738_ = v___x_3747_;
                    v_bs_3739_ = v___x_3749_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(
    mut v_a_3751_: *mut LeanObject,
    mut v_sz_3752_: *mut LeanObject,
    mut v_i_3753_: *mut LeanObject,
    mut v_bs_3754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3755_: usize = 0;
    let mut v_i_boxed_3756_: usize = 0;
    let mut v_res_3757_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3755_ = lean_unbox_usize(v_sz_3752_);
    lean_dec(v_sz_3752_);
    v_i_boxed_3756_ = lean_unbox_usize(v_i_3753_);
    lean_dec(v_i_3753_);
    v_res_3757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_3751_, v_sz_boxed_3755_, v_i_boxed_3756_, v_bs_3754_);
    lean_dec_ref(v_a_3751_);
    return v_res_3757_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(
    mut v_a_3758_: *mut LeanObject,
    mut v_sz_3759_: usize,
    mut v_i_3760_: usize,
    mut v_bs_3761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3762_: u8 = 0;
    v___x_3762_ = lean_usize_dec_lt(v_i_3760_, v_sz_3759_);
    if v___x_3762_ == 0 {
        return v_bs_3761_;
    } else {
        let mut v_v_3763_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fvarId_3764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
        let mut v_bs_x27_3766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3767_: u8 = 0;
        let mut v___x_3768_: usize = 0;
        let mut v___x_3769_: usize = 0;
        let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
        v_v_3763_ = lean_array_uget_borrowed(v_bs_3761_, v_i_3760_);
        v_fvarId_3764_ = lean_ctor_get(v_v_3763_, 0);
        lean_inc(v_fvarId_3764_);
        v___x_3765_ = lean_unsigned_to_nat(0);
        v_bs_x27_3766_ = lean_array_uset(v_bs_3761_, v_i_3760_, v___x_3765_);
        v___x_3767_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3758_, v_fvarId_3764_);
        lean_dec(v_fvarId_3764_);
        v___x_3768_ = 1usize;
        v___x_3769_ = lean_usize_add(v_i_3760_, v___x_3768_);
        v___x_3770_ = lean_box((v___x_3767_) as usize);
        v___x_3771_ = lean_array_uset(v_bs_x27_3766_, v_i_3760_, v___x_3770_);
        v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_3758_, v_sz_3759_, v___x_3769_, v___x_3771_);
        return v___x_3772_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(
    mut v_a_3773_: *mut LeanObject,
    mut v_sz_3774_: *mut LeanObject,
    mut v_i_3775_: *mut LeanObject,
    mut v_bs_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3777_: usize = 0;
    let mut v_i_boxed_3778_: usize = 0;
    let mut v_res_3779_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3777_ = lean_unbox_usize(v_sz_3774_);
    lean_dec(v_sz_3774_);
    v_i_boxed_3778_ = lean_unbox_usize(v_i_3775_);
    lean_dec(v_i_3775_);
    v_res_3779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_3773_, v_sz_boxed_3777_, v_i_boxed_3778_, v_bs_3776_);
    lean_dec_ref(v_a_3773_);
    return v_res_3779_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(
    mut v_a_3780_: *mut LeanObject,
    mut v_as_3781_: *mut LeanObject,
    mut v_i_3782_: usize,
    mut v_stop_3783_: usize,
    mut v_b_3784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: usize = 0;
    let mut v___x_3788_: usize = 0;
    let mut v___x_3790_: u8 = 0;
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: u8 = 0;
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3790_ = lean_usize_dec_eq(v_i_3782_, v_stop_3783_);
                if v___x_3790_ == 0 {
                    v___x_3791_ = lean_array_uget_borrowed(v_as_3781_, v_i_3782_);
                    v_fvarId_3792_ = lean_ctor_get(v___x_3791_, 0);
                    v___x_3793_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3780_, v_fvarId_3792_);
                    if v___x_3793_ == 0 {
                        lean_inc(v___x_3791_);
                        v___x_3794_ = lean_array_push(v_b_3784_, v___x_3791_);
                        v___y_3786_ = v___x_3794_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3786_ = v_b_3784_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3784_;
                }
            }
            1 => {
                v___x_3787_ = 1usize;
                v___x_3788_ = lean_usize_add(v_i_3782_, v___x_3787_);
                v_i_3782_ = v___x_3788_;
                v_b_3784_ = v___y_3786_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(
    mut v_a_3795_: *mut LeanObject,
    mut v_as_3796_: *mut LeanObject,
    mut v_i_3797_: *mut LeanObject,
    mut v_stop_3798_: *mut LeanObject,
    mut v_b_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3800_: usize = 0;
    let mut v_stop_boxed_3801_: usize = 0;
    let mut v_res_3802_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3800_ = lean_unbox_usize(v_i_3797_);
    lean_dec(v_i_3797_);
    v_stop_boxed_3801_ = lean_unbox_usize(v_stop_3798_);
    lean_dec(v_stop_3798_);
    v_res_3802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_3795_, v_as_3796_, v_i_boxed_3800_, v_stop_boxed_3801_, v_b_3799_);
    lean_dec_ref(v_as_3796_);
    lean_dec_ref(v_a_3795_);
    return v_res_3802_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0() -> *mut LeanObject {
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    v___x_3803_ = lean_box(0);
    v___x_3804_ = lean_unsigned_to_nat(16);
    v___x_3805_ = lean_mk_array(v___x_3804_, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13() -> *mut LeanObject {
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    v___x_3826_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
    v___x_3827_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12;
    v___x_3828_ = l_Lean_Name_append(v___x_3827_, v___x_3826_);
    return v___x_3828_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15() -> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
    v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
    return v___x_3831_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_reduceArity(
    mut v_decl_3832_: *mut LeanObject,
    mut v_a_3833_: *mut LeanObject,
    mut v_a_3834_: *mut LeanObject,
    mut v_a_3835_: *mut LeanObject,
    mut v_a_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_3840_: u8 = 0;
    let mut v_inlineAttr_x3f_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v_size_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_safe_3854_: u8 = 0;
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___y_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3866_: usize = 0;
    let mut v___y_3867_: u8 = 0;
    let mut v___y_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: u8 = 0;
    let mut v___y_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: usize = 0;
    let mut v___y_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3894_: usize = 0;
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v_unused_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_a_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_reuseFailAlloc_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3948_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut v_isSharedCheck_3953_: u8 = 0;
    let mut v_unused_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3962_: u8 = 0;
    let mut v_a_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_a_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_reuseFailAlloc_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_a_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3991_: u8 = 0;
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_a_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4010_: usize = 0;
    let mut v___y_4011_: u8 = 0;
    let mut v___y_4012_: usize = 0;
    let mut v___y_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: usize = 0;
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: usize = 0;
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: u8 = 0;
    let mut v___y_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4033_: usize = 0;
    let mut v___x_4034_: usize = 0;
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: u8 = 0;
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: usize = 0;
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: usize = 0;
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4048_: u8 = 0;
    let mut v___y_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v___y_4066_: u8 = 0;
    let mut v_options_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4068_: u8 = 0;
    let mut v_inheritedTraceOptions_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: usize = 0;
    let mut v___x_4081_: usize = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: u8 = 0;
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_a_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4097_: u8 = 0;
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4101_: u8 = 0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_unused_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_3838_ = lean_ctor_get(v_decl_3832_, 1);
                lean_inc_ref(v_value_3838_);
                if lean_obj_tag(v_value_3838_) == 0 {
                    v_toSignature_3839_ = lean_ctor_get(v_decl_3832_, 0);
                    lean_inc_ref(v_toSignature_3839_);
                    v_recursive_3840_ = lean_ctor_get_uint8(
                        v_decl_3832_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_3841_ = lean_ctor_get(v_decl_3832_, 2);
                    v_code_3842_ = lean_ctor_get(v_value_3838_, 0);
                    lean_inc_ref(v_code_3842_);
                    lean_inc_ref(v_decl_3832_);
                    v___x_3843_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(
                        v_decl_3832_,
                        v_a_3833_,
                        v_a_3834_,
                        v_a_3835_,
                        v_a_3836_,
                    );
                    if lean_obj_tag(v___x_3843_) == 0 {
                        v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_4093_ = (!lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_4093_ == 0 {
                            v___x_3846_ = v___x_3843_;
                            v_isShared_3847_ = v_isSharedCheck_4093_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3844_);
                            lean_dec(v___x_3843_);
                            v___x_3846_ = lean_box(0);
                            v_isShared_3847_ = v_isSharedCheck_4093_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_code_3842_);
                        lean_dec_ref(v_toSignature_3839_);
                        lean_dec_ref_known(v_value_3838_, 1);
                        lean_dec_ref(v_decl_3832_);
                        v_a_4094_ = lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_4101_ = (!lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_4101_ == 0 {
                            v___x_4096_ = v___x_3843_;
                            v_isShared_4097_ = v_isSharedCheck_4101_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_4094_);
                            lean_dec(v___x_3843_);
                            v___x_4096_ = lean_box(0);
                            v_isShared_4097_ = v_isSharedCheck_4101_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    v_isSharedCheck_4111_ = (!lean_is_exclusive(v_value_3838_)) as u8;
                    if v_isSharedCheck_4111_ == 0 {
                        v_unused_4112_ = lean_ctor_get(v_value_3838_, 0);
                        lean_dec(v_unused_4112_);
                        v___x_4103_ = v_value_3838_;
                        v_isShared_4104_ = v_isSharedCheck_4111_;
                        state = 36;
                        continue;
                    } else {
                        lean_dec(v_value_3838_);
                        v___x_4103_ = lean_box(0);
                        v_isShared_4104_ = v_isSharedCheck_4111_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                v_size_3848_ = lean_ctor_get(v_a_3844_, 0);
                v_buckets_3849_ = lean_ctor_get(v_a_3844_, 1);
                v_name_3850_ = lean_ctor_get(v_toSignature_3839_, 0);
                v_levelParams_3851_ = lean_ctor_get(v_toSignature_3839_, 1);
                v_type_3852_ = lean_ctor_get(v_toSignature_3839_, 2);
                v_params_3853_ = lean_ctor_get(v_toSignature_3839_, 3);
                v_safe_3854_ = lean_ctor_get_uint8(
                    v_toSignature_3839_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_4092_ = (!lean_is_exclusive(v_toSignature_3839_)) as u8;
                if v_isSharedCheck_4092_ == 0 {
                    v___x_3856_ = v_toSignature_3839_;
                    v_isShared_3857_ = v_isSharedCheck_4092_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_params_3853_);
                    lean_inc(v_type_3852_);
                    lean_inc(v_levelParams_3851_);
                    lean_inc(v_name_3850_);
                    lean_dec(v_toSignature_3839_);
                    v___x_3856_ = lean_box(0);
                    v_isShared_3857_ = v_isSharedCheck_4092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4004_ = lean_array_get_size(v_params_3853_);
                v___x_4089_ = lean_nat_dec_eq(v_size_3848_, v___x_4004_);
                if v___x_4089_ == 0 {
                    v___x_4090_ = lean_unsigned_to_nat(0);
                    v___x_4091_ = lean_nat_dec_eq(v_size_3848_, v___x_4090_);
                    v___y_4066_ = v___x_4091_;
                    state = 32;
                    continue;
                } else {
                    v___y_4066_ = v___x_4089_;
                    state = 32;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___y_3864_);
                v___x_3874_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___y_3864_, v_value_3838_, v___y_3868_, v___y_3865_, v___y_3862_, v___y_3860_, v___y_3870_);
                lean_dec_ref(v___y_3868_);
                if lean_obj_tag(v___x_3874_) == 0 {
                    v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
                    lean_inc(v_a_3875_);
                    lean_dec_ref_known(v___x_3874_, 1);
                    v___x_3876_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___y_3869_,
                        v_code_3842_,
                        v___y_3865_,
                        v___y_3862_,
                        v___y_3860_,
                        v___y_3870_,
                    );
                    if lean_obj_tag(v___x_3876_) == 0 {
                        v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
                        lean_inc(v_a_3877_);
                        lean_dec_ref_known(v___x_3876_, 1);
                        lean_inc_ref(v___y_3861_);
                        v___x_3878_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___y_3869_,
                            v___y_3861_,
                            v_a_3877_,
                            v___y_3865_,
                            v___y_3862_,
                            v___y_3860_,
                            v___y_3870_,
                        );
                        lean_dec(v_a_3877_);
                        if lean_obj_tag(v___x_3878_) == 0 {
                            v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
                            lean_inc(v_a_3879_);
                            lean_dec_ref_known(v___x_3878_, 1);
                            v___x_3880_ = lean_box(0);
                            lean_inc(v___y_3859_);
                            if v_isShared_3857_ == 0 {
                                lean_ctor_set(v___x_3856_, 3, v___y_3861_);
                                lean_ctor_set(v___x_3856_, 2, v_a_3879_);
                                lean_ctor_set(v___x_3856_, 1, v___x_3880_);
                                lean_ctor_set(v___x_3856_, 0, v___y_3859_);
                                v___x_3882_ = v___x_3856_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 4, (1) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___y_3859_);
                                lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3880_);
                                lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_a_3879_);
                                lean_ctor_set(v_reuseFailAlloc_3979_, 3, v___y_3861_);
                                lean_ctor_set_uint8(
                                    v_reuseFailAlloc_3979_,
                                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                                    v_safe_3854_,
                                );
                                v___x_3882_ = v_reuseFailAlloc_3979_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3875_);
                            lean_dec_ref(v___y_3873_);
                            lean_dec(v___y_3872_);
                            lean_dec_ref(v___y_3863_);
                            lean_dec_ref(v___y_3861_);
                            lean_dec(v___y_3859_);
                            lean_del_object(v___x_3856_);
                            lean_dec_ref(v_params_3853_);
                            lean_dec_ref(v_type_3852_);
                            lean_dec(v_levelParams_3851_);
                            lean_dec(v_name_3850_);
                            lean_dec(v_inlineAttr_x3f_3841_);
                            v_a_3980_ = lean_ctor_get(v___x_3878_, 0);
                            v_isSharedCheck_3987_ = (!lean_is_exclusive(v___x_3878_)) as u8;
                            if v_isSharedCheck_3987_ == 0 {
                                v___x_3982_ = v___x_3878_;
                                v_isShared_3983_ = v_isSharedCheck_3987_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_3980_);
                                lean_dec(v___x_3878_);
                                v___x_3982_ = lean_box(0);
                                v_isShared_3983_ = v_isSharedCheck_3987_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3875_);
                        lean_dec_ref(v___y_3873_);
                        lean_dec(v___y_3872_);
                        lean_dec_ref(v___y_3863_);
                        lean_dec_ref(v___y_3861_);
                        lean_dec(v___y_3859_);
                        lean_del_object(v___x_3856_);
                        lean_dec_ref(v_params_3853_);
                        lean_dec_ref(v_type_3852_);
                        lean_dec(v_levelParams_3851_);
                        lean_dec(v_name_3850_);
                        lean_dec(v_inlineAttr_x3f_3841_);
                        v_a_3988_ = lean_ctor_get(v___x_3876_, 0);
                        v_isSharedCheck_3995_ = (!lean_is_exclusive(v___x_3876_)) as u8;
                        if v_isSharedCheck_3995_ == 0 {
                            v___x_3990_ = v___x_3876_;
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3988_);
                            lean_dec(v___x_3876_);
                            v___x_3990_ = lean_box(0);
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3873_);
                    lean_dec(v___y_3872_);
                    lean_dec_ref(v___y_3863_);
                    lean_dec_ref(v___y_3861_);
                    lean_dec(v___y_3859_);
                    lean_del_object(v___x_3856_);
                    lean_dec_ref(v_params_3853_);
                    lean_dec_ref(v_type_3852_);
                    lean_dec(v_levelParams_3851_);
                    lean_dec(v_name_3850_);
                    lean_dec_ref(v_code_3842_);
                    lean_dec(v_inlineAttr_x3f_3841_);
                    v_a_3996_ = lean_ctor_get(v___x_3874_, 0);
                    v_isSharedCheck_4003_ = (!lean_is_exclusive(v___x_3874_)) as u8;
                    if v_isSharedCheck_4003_ == 0 {
                        v___x_3998_ = v___x_3874_;
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_3996_);
                        lean_dec(v___x_3874_);
                        v___x_3998_ = lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 25;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3883_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3883_, 0, v___x_3882_);
                lean_ctor_set(v___x_3883_, 1, v_a_3875_);
                lean_ctor_set(v___x_3883_, 2, v_inlineAttr_x3f_3841_);
                lean_ctor_set_uint8(
                    v___x_3883_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v_recursive_3840_,
                );
                lean_inc_ref(v___x_3883_);
                v___x_3884_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_3883_, v___y_3870_);
                if lean_obj_tag(v___x_3884_) == 0 {
                    lean_dec_ref_known(v___x_3884_, 1);
                    v___x_3885_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0,
                    );
                    lean_inc(v___y_3872_);
                    v___x_3886_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3886_, 0, v___y_3872_);
                    lean_ctor_set(v___x_3886_, 1, v___x_3885_);
                    v___x_3887_ = lean_st_mk_ref(v___x_3886_);
                    v___x_3888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_3866_, v___y_3871_, v_params_3853_, v___y_3867_, v___x_3887_, v___y_3865_, v___y_3862_, v___y_3860_, v___y_3870_);
                    if lean_obj_tag(v___x_3888_) == 0 {
                        v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
                        lean_inc_n(v_a_3889_, 2);
                        lean_dec_ref_known(v___x_3888_, 1);
                        v___x_3890_ = lean_mk_empty_array_with_capacity(v___y_3872_);
                        v___x_3891_ = lean_array_get_size(v_a_3889_);
                        v___x_3892_ =
                            l_Array_toSubarray___redArg(v_a_3889_, v___y_3872_, v___x_3891_);
                        v___x_3893_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3893_, 0, v___x_3890_);
                        lean_ctor_set(v___x_3893_, 1, v___x_3892_);
                        v_sz_3894_ = lean_array_size(v___y_3863_);
                        v___x_3895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_3863_, v_sz_3894_, v___y_3871_, v___x_3893_);
                        lean_dec_ref(v___y_3863_);
                        if lean_obj_tag(v___x_3895_) == 0 {
                            v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
                            lean_inc(v_a_3896_);
                            lean_dec_ref_known(v___x_3895_, 1);
                            v_fst_3897_ = lean_ctor_get(v_a_3896_, 0);
                            v_isSharedCheck_3953_ = (!lean_is_exclusive(v_a_3896_)) as u8;
                            if v_isSharedCheck_3953_ == 0 {
                                v_unused_3954_ = lean_ctor_get(v_a_3896_, 1);
                                lean_dec(v_unused_3954_);
                                v___x_3899_ = v_a_3896_;
                                v_isShared_3900_ = v_isSharedCheck_3953_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_fst_3897_);
                                lean_dec(v_a_3896_);
                                v___x_3899_ = lean_box(0);
                                v_isShared_3900_ = v_isSharedCheck_3953_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3889_);
                            lean_dec(v___x_3887_);
                            lean_dec_ref_known(v___x_3883_, 3);
                            lean_dec_ref(v___y_3873_);
                            lean_dec(v___y_3859_);
                            lean_dec_ref(v_type_3852_);
                            lean_dec(v_levelParams_3851_);
                            lean_dec(v_name_3850_);
                            v_a_3955_ = lean_ctor_get(v___x_3895_, 0);
                            v_isSharedCheck_3962_ = (!lean_is_exclusive(v___x_3895_)) as u8;
                            if v_isSharedCheck_3962_ == 0 {
                                v___x_3957_ = v___x_3895_;
                                v_isShared_3958_ = v_isSharedCheck_3962_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_3955_);
                                lean_dec(v___x_3895_);
                                v___x_3957_ = lean_box(0);
                                v_isShared_3958_ = v_isSharedCheck_3962_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3887_);
                        lean_dec_ref_known(v___x_3883_, 3);
                        lean_dec_ref(v___y_3873_);
                        lean_dec(v___y_3872_);
                        lean_dec_ref(v___y_3863_);
                        lean_dec(v___y_3859_);
                        lean_dec_ref(v_type_3852_);
                        lean_dec(v_levelParams_3851_);
                        lean_dec(v_name_3850_);
                        v_a_3963_ = lean_ctor_get(v___x_3888_, 0);
                        v_isSharedCheck_3970_ = (!lean_is_exclusive(v___x_3888_)) as u8;
                        if v_isSharedCheck_3970_ == 0 {
                            v___x_3965_ = v___x_3888_;
                            v_isShared_3966_ = v_isSharedCheck_3970_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3963_);
                            lean_dec(v___x_3888_);
                            v___x_3965_ = lean_box(0);
                            v_isShared_3966_ = v_isSharedCheck_3970_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_3883_, 3);
                    lean_dec_ref(v___y_3873_);
                    lean_dec(v___y_3872_);
                    lean_dec_ref(v___y_3863_);
                    lean_dec(v___y_3859_);
                    lean_dec_ref(v_params_3853_);
                    lean_dec_ref(v_type_3852_);
                    lean_dec(v_levelParams_3851_);
                    lean_dec(v_name_3850_);
                    v_a_3971_ = lean_ctor_get(v___x_3884_, 0);
                    v_isSharedCheck_3978_ = (!lean_is_exclusive(v___x_3884_)) as u8;
                    if v_isSharedCheck_3978_ == 0 {
                        v___x_3973_ = v___x_3884_;
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3971_);
                        lean_dec(v___x_3884_);
                        v___x_3973_ = lean_box(0);
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 19;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3901_ = lean_alloc_ctor(3, 3, (0) as u32);
                lean_ctor_set(v___x_3901_, 0, v___y_3859_);
                lean_ctor_set(v___x_3901_, 1, v___x_3880_);
                lean_ctor_set(v___x_3901_, 2, v_fst_3897_);
                v___x_3902_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
                v___x_3903_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
                    v___y_3869_,
                    v___x_3901_,
                    v___x_3902_,
                    v___y_3865_,
                    v___y_3862_,
                    v___y_3860_,
                    v___y_3870_,
                );
                if lean_obj_tag(v___x_3903_) == 0 {
                    v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
                    lean_inc(v_a_3904_);
                    lean_dec_ref_known(v___x_3903_, 1);
                    v_fvarId_3905_ = lean_ctor_get(v_a_3904_, 0);
                    lean_inc(v_fvarId_3905_);
                    v___x_3906_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v___x_3906_, 0, v_fvarId_3905_);
                    if v_isShared_3900_ == 0 {
                        lean_ctor_set(v___x_3899_, 1, v___x_3906_);
                        lean_ctor_set(v___x_3899_, 0, v_a_3904_);
                        v___x_3908_ = v___x_3899_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3904_);
                        lean_ctor_set(v_reuseFailAlloc_3944_, 1, v___x_3906_);
                        v___x_3908_ = v_reuseFailAlloc_3944_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3899_);
                    lean_dec(v_a_3889_);
                    lean_dec(v___x_3887_);
                    lean_dec_ref_known(v___x_3883_, 3);
                    lean_dec_ref(v___y_3873_);
                    lean_dec_ref(v_type_3852_);
                    lean_dec(v_levelParams_3851_);
                    lean_dec(v_name_3850_);
                    v_a_3945_ = lean_ctor_get(v___x_3903_, 0);
                    v_isSharedCheck_3952_ = (!lean_is_exclusive(v___x_3903_)) as u8;
                    if v_isSharedCheck_3952_ == 0 {
                        v___x_3947_ = v___x_3903_;
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3945_);
                        lean_dec(v___x_3903_);
                        v___x_3947_ = lean_box(0);
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3909_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3909_, 0, v___x_3908_);
                v___x_3910_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_3910_, 0, v_name_3850_);
                lean_ctor_set(v___x_3910_, 1, v_levelParams_3851_);
                lean_ctor_set(v___x_3910_, 2, v_type_3852_);
                lean_ctor_set(v___x_3910_, 3, v_a_3889_);
                lean_ctor_set_uint8(
                    v___x_3910_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v_safe_3854_,
                );
                v___x_3911_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
                v___x_3912_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3912_, 0, v___x_3910_);
                lean_ctor_set(v___x_3912_, 1, v___x_3909_);
                lean_ctor_set(v___x_3912_, 2, v___x_3911_);
                lean_ctor_set_uint8(
                    v___x_3912_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___y_3867_,
                );
                lean_inc_ref(v___x_3912_);
                v___x_3913_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_3912_, v___y_3870_);
                if lean_obj_tag(v___x_3913_) == 0 {
                    lean_dec_ref_known(v___x_3913_, 1);
                    v___x_3914_ = lean_st_ref_get(v___x_3887_);
                    lean_dec(v___x_3887_);
                    lean_dec(v___x_3914_);
                    v___x_3915_ = l_Lean_Compiler_LCNF_eraseParams___redArg(
                        v___y_3869_,
                        v___y_3873_,
                        v___y_3862_,
                    );
                    lean_dec_ref(v___y_3873_);
                    if lean_obj_tag(v___x_3915_) == 0 {
                        v_isSharedCheck_3926_ = (!lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3926_ == 0 {
                            v_unused_3927_ = lean_ctor_get(v___x_3915_, 0);
                            lean_dec(v_unused_3927_);
                            v___x_3917_ = v___x_3915_;
                            v_isShared_3918_ = v_isSharedCheck_3926_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_3915_);
                            v___x_3917_ = lean_box(0);
                            v_isShared_3918_ = v_isSharedCheck_3926_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_3912_, 3);
                        lean_dec_ref_known(v___x_3883_, 3);
                        v_a_3928_ = lean_ctor_get(v___x_3915_, 0);
                        v_isSharedCheck_3935_ = (!lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3935_ == 0 {
                            v___x_3930_ = v___x_3915_;
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3928_);
                            lean_dec(v___x_3915_);
                            v___x_3930_ = lean_box(0);
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_3912_, 3);
                    lean_dec(v___x_3887_);
                    lean_dec_ref_known(v___x_3883_, 3);
                    lean_dec_ref(v___y_3873_);
                    v_a_3936_ = lean_ctor_get(v___x_3913_, 0);
                    v_isSharedCheck_3943_ = (!lean_is_exclusive(v___x_3913_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v___x_3938_ = v___x_3913_;
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3936_);
                        lean_dec(v___x_3913_);
                        v___x_3938_ = lean_box(0);
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3919_ = lean_unsigned_to_nat(2);
                v___x_3920_ = lean_mk_empty_array_with_capacity(v___x_3919_);
                v___x_3921_ = lean_array_push(v___x_3920_, v___x_3883_);
                v___x_3922_ = lean_array_push(v___x_3921_, v___x_3912_);
                if v_isShared_3918_ == 0 {
                    lean_ctor_set(v___x_3917_, 0, v___x_3922_);
                    v___x_3924_ = v___x_3917_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3924_;
            }
            9 => {
                if v_isShared_3931_ == 0 {
                    v___x_3933_ = v___x_3930_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3933_;
            }
            11 => {
                if v_isShared_3939_ == 0 {
                    v___x_3941_ = v___x_3938_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3941_;
            }
            13 => {
                if v_isShared_3948_ == 0 {
                    v___x_3950_ = v___x_3947_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
                    v___x_3950_ = v_reuseFailAlloc_3951_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3950_;
            }
            15 => {
                if v_isShared_3958_ == 0 {
                    v___x_3960_ = v___x_3957_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
                    v___x_3960_ = v_reuseFailAlloc_3961_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3960_;
            }
            17 => {
                if v_isShared_3966_ == 0 {
                    v___x_3968_ = v___x_3965_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
                    v___x_3968_ = v_reuseFailAlloc_3969_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3968_;
            }
            19 => {
                if v_isShared_3974_ == 0 {
                    v___x_3976_ = v___x_3973_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3976_;
            }
            21 => {
                if v_isShared_3983_ == 0 {
                    v___x_3985_ = v___x_3982_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
                    v___x_3985_ = v_reuseFailAlloc_3986_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3985_;
            }
            23 => {
                if v_isShared_3991_ == 0 {
                    v___x_3993_ = v___x_3990_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
                    v___x_3993_ = v_reuseFailAlloc_3994_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3993_;
            }
            25 => {
                if v_isShared_3999_ == 0 {
                    v___x_4001_ = v___x_3998_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
                    v___x_4001_ = v_reuseFailAlloc_4002_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4001_;
            }
            27 => {
                v___x_4017_ = 0;
                v___x_4018_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
                lean_inc_ref(v___y_4007_);
                lean_inc(v___y_4006_);
                lean_inc(v_name_3850_);
                v___x_4019_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4019_, 0, v_name_3850_);
                lean_ctor_set(v___x_4019_, 1, v___y_4006_);
                lean_ctor_set(v___x_4019_, 2, v___y_4007_);
                v___x_4020_ = lean_mk_empty_array_with_capacity(v___y_4015_);
                v___x_4021_ = lean_nat_dec_lt(v___y_4015_, v___x_4004_);
                if v___x_4021_ == 0 {
                    lean_dec(v_a_3844_);
                    v___y_3859_ = v___y_4006_;
                    v___y_3860_ = v___y_4008_;
                    v___y_3861_ = v___y_4016_;
                    v___y_3862_ = v___y_4014_;
                    v___y_3863_ = v___y_4007_;
                    v___y_3864_ = v___x_4018_;
                    v___y_3865_ = v___y_4009_;
                    v___y_3866_ = v___y_4010_;
                    v___y_3867_ = v___y_4011_;
                    v___y_3868_ = v___x_4019_;
                    v___y_3869_ = v___x_4017_;
                    v___y_3870_ = v___y_4013_;
                    v___y_3871_ = v___y_4012_;
                    v___y_3872_ = v___y_4015_;
                    v___y_3873_ = v___x_4020_;
                    state = 3;
                    continue;
                } else {
                    v___x_4022_ = lean_nat_dec_le(v___x_4004_, v___x_4004_);
                    if v___x_4022_ == 0 {
                        if v___x_4021_ == 0 {
                            lean_dec(v_a_3844_);
                            v___y_3859_ = v___y_4006_;
                            v___y_3860_ = v___y_4008_;
                            v___y_3861_ = v___y_4016_;
                            v___y_3862_ = v___y_4014_;
                            v___y_3863_ = v___y_4007_;
                            v___y_3864_ = v___x_4018_;
                            v___y_3865_ = v___y_4009_;
                            v___y_3866_ = v___y_4010_;
                            v___y_3867_ = v___y_4011_;
                            v___y_3868_ = v___x_4019_;
                            v___y_3869_ = v___x_4017_;
                            v___y_3870_ = v___y_4013_;
                            v___y_3871_ = v___y_4012_;
                            v___y_3872_ = v___y_4015_;
                            v___y_3873_ = v___x_4020_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4023_ = lean_usize_of_nat(v___x_4004_);
                            v___x_4024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_3844_, v_params_3853_, v___y_4012_, v___x_4023_, v___x_4020_);
                            lean_dec(v_a_3844_);
                            v___y_3859_ = v___y_4006_;
                            v___y_3860_ = v___y_4008_;
                            v___y_3861_ = v___y_4016_;
                            v___y_3862_ = v___y_4014_;
                            v___y_3863_ = v___y_4007_;
                            v___y_3864_ = v___x_4018_;
                            v___y_3865_ = v___y_4009_;
                            v___y_3866_ = v___y_4010_;
                            v___y_3867_ = v___y_4011_;
                            v___y_3868_ = v___x_4019_;
                            v___y_3869_ = v___x_4017_;
                            v___y_3870_ = v___y_4013_;
                            v___y_3871_ = v___y_4012_;
                            v___y_3872_ = v___y_4015_;
                            v___y_3873_ = v___x_4024_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4025_ = lean_usize_of_nat(v___x_4004_);
                        v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_3844_, v_params_3853_, v___y_4012_, v___x_4025_, v___x_4020_);
                        lean_dec(v_a_3844_);
                        v___y_3859_ = v___y_4006_;
                        v___y_3860_ = v___y_4008_;
                        v___y_3861_ = v___y_4016_;
                        v___y_3862_ = v___y_4014_;
                        v___y_3863_ = v___y_4007_;
                        v___y_3864_ = v___x_4018_;
                        v___y_3865_ = v___y_4009_;
                        v___y_3866_ = v___y_4010_;
                        v___y_3867_ = v___y_4011_;
                        v___y_3868_ = v___x_4019_;
                        v___y_3869_ = v___x_4017_;
                        v___y_3870_ = v___y_4013_;
                        v___y_3871_ = v___y_4012_;
                        v___y_3872_ = v___y_4015_;
                        v___y_3873_ = v___x_4026_;
                        state = 3;
                        continue;
                    }
                }
            }
            28 => {
                v_sz_4033_ = lean_array_size(v_params_3853_);
                v___x_4034_ = 0usize;
                lean_inc_ref(v_params_3853_);
                v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_3844_, v_sz_4033_, v___x_4034_, v_params_3853_);
                v___x_4036_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
                lean_inc(v_name_3850_);
                v___x_4037_ = l_Lean_Name_append(v_name_3850_, v___x_4036_);
                v___x_4038_ = lean_unsigned_to_nat(0);
                v___x_4039_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
                v___x_4040_ = lean_nat_dec_lt(v___x_4038_, v___x_4004_);
                if v___x_4040_ == 0 {
                    v___y_4006_ = v___x_4037_;
                    v___y_4007_ = v___x_4035_;
                    v___y_4008_ = v___y_4031_;
                    v___y_4009_ = v___y_4029_;
                    v___y_4010_ = v_sz_4033_;
                    v___y_4011_ = v___y_4028_;
                    v___y_4012_ = v___x_4034_;
                    v___y_4013_ = v___y_4032_;
                    v___y_4014_ = v___y_4030_;
                    v___y_4015_ = v___x_4038_;
                    v___y_4016_ = v___x_4039_;
                    state = 27;
                    continue;
                } else {
                    v___x_4041_ = lean_nat_dec_le(v___x_4004_, v___x_4004_);
                    if v___x_4041_ == 0 {
                        if v___x_4040_ == 0 {
                            v___y_4006_ = v___x_4037_;
                            v___y_4007_ = v___x_4035_;
                            v___y_4008_ = v___y_4031_;
                            v___y_4009_ = v___y_4029_;
                            v___y_4010_ = v_sz_4033_;
                            v___y_4011_ = v___y_4028_;
                            v___y_4012_ = v___x_4034_;
                            v___y_4013_ = v___y_4032_;
                            v___y_4014_ = v___y_4030_;
                            v___y_4015_ = v___x_4038_;
                            v___y_4016_ = v___x_4039_;
                            state = 27;
                            continue;
                        } else {
                            v___x_4042_ = lean_usize_of_nat(v___x_4004_);
                            v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_3844_, v_params_3853_, v___x_4034_, v___x_4042_, v___x_4039_);
                            v___y_4006_ = v___x_4037_;
                            v___y_4007_ = v___x_4035_;
                            v___y_4008_ = v___y_4031_;
                            v___y_4009_ = v___y_4029_;
                            v___y_4010_ = v_sz_4033_;
                            v___y_4011_ = v___y_4028_;
                            v___y_4012_ = v___x_4034_;
                            v___y_4013_ = v___y_4032_;
                            v___y_4014_ = v___y_4030_;
                            v___y_4015_ = v___x_4038_;
                            v___y_4016_ = v___x_4043_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v___x_4044_ = lean_usize_of_nat(v___x_4004_);
                        v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_3844_, v_params_3853_, v___x_4034_, v___x_4044_, v___x_4039_);
                        v___y_4006_ = v___x_4037_;
                        v___y_4007_ = v___x_4035_;
                        v___y_4008_ = v___y_4031_;
                        v___y_4009_ = v___y_4029_;
                        v___y_4010_ = v_sz_4033_;
                        v___y_4011_ = v___y_4028_;
                        v___y_4012_ = v___x_4034_;
                        v___y_4013_ = v___y_4032_;
                        v___y_4014_ = v___y_4030_;
                        v___y_4015_ = v___x_4038_;
                        v___y_4016_ = v___x_4045_;
                        state = 27;
                        continue;
                    }
                }
            }
            29 => {
                v___x_4051_ = lean_box(0);
                v___x_4052_ =
                    l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(
                        v___y_4050_,
                        v___x_4051_,
                    );
                v___x_4053_ =
                    l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(
                        v___x_4052_,
                        v___x_4051_,
                    );
                v___x_4054_ = l_Lean_MessageData_ofList(v___x_4053_);
                v___x_4055_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4055_, 0, v___y_4049_);
                lean_ctor_set(v___x_4055_, 1, v___x_4054_);
                lean_inc(v___y_4047_);
                v___x_4056_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(
                    v___y_4047_,
                    v___x_4055_,
                    v_a_3833_,
                    v_a_3834_,
                    v_a_3835_,
                    v_a_3836_,
                );
                if lean_obj_tag(v___x_4056_) == 0 {
                    lean_dec_ref_known(v___x_4056_, 1);
                    v___y_4028_ = v___y_4048_;
                    v___y_4029_ = v_a_3833_;
                    v___y_4030_ = v_a_3834_;
                    v___y_4031_ = v_a_3835_;
                    v___y_4032_ = v_a_3836_;
                    state = 28;
                    continue;
                } else {
                    lean_del_object(v___x_3856_);
                    lean_dec_ref(v_params_3853_);
                    lean_dec_ref(v_type_3852_);
                    lean_dec(v_levelParams_3851_);
                    lean_dec(v_name_3850_);
                    lean_dec(v_a_3844_);
                    lean_dec_ref(v_code_3842_);
                    lean_dec(v_inlineAttr_x3f_3841_);
                    lean_dec_ref_known(v_value_3838_, 1);
                    v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4064_ = (!lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4064_ == 0 {
                        v___x_4059_ = v___x_4056_;
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_4057_);
                        lean_dec(v___x_4056_);
                        v___x_4059_ = lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 30;
                        continue;
                    }
                }
            }
            30 => {
                if v_isShared_4060_ == 0 {
                    v___x_4062_ = v___x_4059_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4062_;
            }
            32 => {
                if v___y_4066_ == 0 {
                    lean_inc(v_inlineAttr_x3f_3841_);
                    lean_del_object(v___x_3846_);
                    lean_dec_ref(v_decl_3832_);
                    v_options_4067_ = lean_ctor_get(v_a_3835_, 2);
                    v_hasTrace_4068_ = lean_ctor_get_uint8(
                        v_options_4067_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4068_ == 0 {
                        v___y_4028_ = v___y_4066_;
                        v___y_4029_ = v_a_3833_;
                        v___y_4030_ = v_a_3834_;
                        v___y_4031_ = v_a_3835_;
                        v___y_4032_ = v_a_3836_;
                        state = 28;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4069_ = lean_ctor_get(v_a_3835_, 13);
                        v___x_4070_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
                        v___x_4071_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13,
                        );
                        v___x_4072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4069_,
                            v_options_4067_,
                            v___x_4071_,
                        );
                        if v___x_4072_ == 0 {
                            v___y_4028_ = v___y_4066_;
                            v___y_4029_ = v_a_3833_;
                            v___y_4030_ = v_a_3834_;
                            v___y_4031_ = v_a_3835_;
                            v___y_4032_ = v_a_3836_;
                            state = 28;
                            continue;
                        } else {
                            lean_inc(v_name_3850_);
                            v___x_4073_ = l_Lean_MessageData_ofName(v_name_3850_);
                            v___x_4074_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15,
                            );
                            v___x_4075_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4075_, 0, v___x_4073_);
                            lean_ctor_set(v___x_4075_, 1, v___x_4074_);
                            v___x_4076_ = lean_box(0);
                            v___x_4077_ = lean_array_get_size(v_buckets_3849_);
                            v___x_4078_ = lean_unsigned_to_nat(0);
                            v___x_4079_ = lean_nat_dec_lt(v___x_4078_, v___x_4077_);
                            if v___x_4079_ == 0 {
                                v___y_4047_ = v___x_4070_;
                                v___y_4048_ = v___y_4066_;
                                v___y_4049_ = v___x_4075_;
                                v___y_4050_ = v___x_4076_;
                                state = 29;
                                continue;
                            } else {
                                v___x_4080_ = lean_usize_of_nat(v___x_4077_);
                                v___x_4081_ = 0usize;
                                v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_3849_, v___x_4080_, v___x_4081_, v___x_4076_);
                                v___y_4047_ = v___x_4070_;
                                v___y_4048_ = v___y_4066_;
                                v___y_4049_ = v___x_4075_;
                                v___y_4050_ = v___x_4082_;
                                state = 29;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_3856_);
                    lean_dec_ref(v_params_3853_);
                    lean_dec_ref(v_type_3852_);
                    lean_dec(v_levelParams_3851_);
                    lean_dec(v_name_3850_);
                    lean_dec(v_a_3844_);
                    lean_dec_ref(v_code_3842_);
                    lean_dec_ref_known(v_value_3838_, 1);
                    v___x_4083_ = lean_unsigned_to_nat(1);
                    v___x_4084_ = lean_mk_empty_array_with_capacity(v___x_4083_);
                    v___x_4085_ = lean_array_push(v___x_4084_, v_decl_3832_);
                    if v_isShared_3847_ == 0 {
                        lean_ctor_set(v___x_3846_, 0, v___x_4085_);
                        v___x_4087_ = v___x_3846_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
                        v___x_4087_ = v_reuseFailAlloc_4088_;
                        state = 33;
                        continue;
                    }
                }
            }
            33 => {
                return v___x_4087_;
            }
            34 => {
                if v_isShared_4097_ == 0 {
                    v___x_4099_ = v___x_4096_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
                    v___x_4099_ = v_reuseFailAlloc_4100_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4099_;
            }
            36 => {
                v___x_4105_ = lean_unsigned_to_nat(1);
                v___x_4106_ = lean_mk_empty_array_with_capacity(v___x_4105_);
                v___x_4107_ = lean_array_push(v___x_4106_, v_decl_3832_);
                if v_isShared_4104_ == 0 {
                    lean_ctor_set_tag(v___x_4103_, 0);
                    lean_ctor_set(v___x_4103_, 0, v___x_4107_);
                    v___x_4109_ = v___x_4103_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
                    v___x_4109_ = v_reuseFailAlloc_4110_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(
    mut v_decl_4113_: *mut LeanObject,
    mut v_a_4114_: *mut LeanObject,
    mut v_a_4115_: *mut LeanObject,
    mut v_a_4116_: *mut LeanObject,
    mut v_a_4117_: *mut LeanObject,
    mut v_a_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4119_: *mut LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_Compiler_LCNF_Decl_reduceArity(
        v_decl_4113_,
        v_a_4114_,
        v_a_4115_,
        v_a_4116_,
        v_a_4117_,
    );
    lean_dec(v_a_4117_);
    lean_dec_ref(v_a_4116_);
    lean_dec(v_a_4115_);
    lean_dec_ref(v_a_4114_);
    return v_res_4119_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(
    mut v_00_u03b2_4120_: *mut LeanObject,
    mut v_m_4121_: *mut LeanObject,
    mut v_a_4122_: *mut LeanObject,
) -> u8 {
    let mut v___x_4123_: u8 = 0;
    v___x_4123_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_4121_, v_a_4122_);
    return v___x_4123_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(
    mut v_00_u03b2_4124_: *mut LeanObject,
    mut v_m_4125_: *mut LeanObject,
    mut v_a_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4127_: u8 = 0;
    let mut v_r_4128_: *mut LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_4124_, v_m_4125_, v_a_4126_);
    lean_dec(v_a_4126_);
    lean_dec_ref(v_m_4125_);
    v_r_4128_ = lean_box((v_res_4127_) as usize);
    return v_r_4128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(
    mut v_as_4129_: *mut LeanObject,
    mut v_sz_4130_: usize,
    mut v_i_4131_: usize,
    mut v_b_4132_: *mut LeanObject,
    mut v___y_4133_: u8,
    mut v___y_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
    mut v___y_4138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    v___x_4140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_4129_, v_sz_4130_, v_i_4131_, v_b_4132_);
    return v___x_4140_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(
    mut v_as_4141_: *mut LeanObject,
    mut v_sz_4142_: *mut LeanObject,
    mut v_i_4143_: *mut LeanObject,
    mut v_b_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4152_: usize = 0;
    let mut v_i_boxed_4153_: usize = 0;
    let mut v___y_13288__boxed_4154_: u8 = 0;
    let mut v_res_4155_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4152_ = lean_unbox_usize(v_sz_4142_);
    lean_dec(v_sz_4142_);
    v_i_boxed_4153_ = lean_unbox_usize(v_i_4143_);
    lean_dec(v_i_4143_);
    v___y_13288__boxed_4154_ = (lean_unbox(v___y_4145_) as u8);
    v_res_4155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_4141_, v_sz_boxed_4152_, v_i_boxed_4153_, v_b_4144_, v___y_13288__boxed_4154_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
    lean_dec(v___y_4150_);
    lean_dec_ref(v___y_4149_);
    lean_dec(v___y_4148_);
    lean_dec_ref(v___y_4147_);
    lean_dec(v___y_4146_);
    lean_dec_ref(v_as_4141_);
    return v_res_4155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(
    mut v_as_4156_: *mut LeanObject,
    mut v_i_4157_: usize,
    mut v_stop_4158_: usize,
    mut v_b_4159_: *mut LeanObject,
    mut v___y_4160_: *mut LeanObject,
    mut v___y_4161_: *mut LeanObject,
    mut v___y_4162_: *mut LeanObject,
    mut v___y_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: usize = 0;
    let mut v___x_4168_: usize = 0;
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4170_ = lean_usize_dec_eq(v_i_4157_, v_stop_4158_);
                if v___x_4170_ == 0 {
                    v___x_4171_ = lean_array_uget_borrowed(v_as_4156_, v_i_4157_);
                    lean_inc(v___x_4171_);
                    v___x_4172_ = l_Lean_Compiler_LCNF_Decl_reduceArity(
                        v___x_4171_,
                        v___y_4160_,
                        v___y_4161_,
                        v___y_4162_,
                        v___y_4163_,
                    );
                    if lean_obj_tag(v___x_4172_) == 0 {
                        v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
                        lean_inc(v_a_4173_);
                        lean_dec_ref_known(v___x_4172_, 1);
                        v___x_4174_ = l_Array_append___redArg(v_b_4159_, v_a_4173_);
                        lean_dec(v_a_4173_);
                        v_a_4166_ = v___x_4174_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_4159_);
                        if lean_obj_tag(v___x_4172_) == 0 {
                            v_a_4175_ = lean_ctor_get(v___x_4172_, 0);
                            lean_inc(v_a_4175_);
                            lean_dec_ref_known(v___x_4172_, 1);
                            v_a_4166_ = v_a_4175_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_4172_;
                        }
                    }
                } else {
                    v___x_4176_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4176_, 0, v_b_4159_);
                    return v___x_4176_;
                }
            }
            1 => {
                v___x_4167_ = 1usize;
                v___x_4168_ = lean_usize_add(v_i_4157_, v___x_4167_);
                v_i_4157_ = v___x_4168_;
                v_b_4159_ = v_a_4166_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(
    mut v_as_4177_: *mut LeanObject,
    mut v_i_4178_: *mut LeanObject,
    mut v_stop_4179_: *mut LeanObject,
    mut v_b_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4186_: usize = 0;
    let mut v_stop_boxed_4187_: usize = 0;
    let mut v_res_4188_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4186_ = lean_unbox_usize(v_i_4178_);
    lean_dec(v_i_4178_);
    v_stop_boxed_4187_ = lean_unbox_usize(v_stop_4179_);
    lean_dec(v_stop_4179_);
    v_res_4188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_4177_, v_i_boxed_4186_, v_stop_boxed_4187_, v_b_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
    lean_dec(v___y_4184_);
    lean_dec_ref(v___y_4183_);
    lean_dec(v___y_4182_);
    lean_dec_ref(v___y_4181_);
    lean_dec_ref(v_as_4177_);
    return v_res_4188_;
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceArity___lam__0(
    mut v___x_4189_: *mut LeanObject,
    mut v_decls_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
    mut v___y_4193_: *mut LeanObject,
    mut v___y_4194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: u8 = 0;
    v___x_4196_ = lean_mk_empty_array_with_capacity(v___x_4189_);
    v___x_4197_ = lean_array_get_size(v_decls_4190_);
    v___x_4198_ = lean_nat_dec_lt(v___x_4189_, v___x_4197_);
    if v___x_4198_ == 0 {
        let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
        v___x_4199_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4199_, 0, v___x_4196_);
        return v___x_4199_;
    } else {
        let mut v___x_4200_: u8 = 0;
        v___x_4200_ = lean_nat_dec_le(v___x_4197_, v___x_4197_);
        if v___x_4200_ == 0 {
            if v___x_4198_ == 0 {
                let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
                v___x_4201_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4201_, 0, v___x_4196_);
                return v___x_4201_;
            } else {
                let mut v___x_4202_: usize = 0;
                let mut v___x_4203_: usize = 0;
                let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
                v___x_4202_ = 0usize;
                v___x_4203_ = lean_usize_of_nat(v___x_4197_);
                v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_4190_, v___x_4202_, v___x_4203_, v___x_4196_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
                return v___x_4204_;
            }
        } else {
            let mut v___x_4205_: usize = 0;
            let mut v___x_4206_: usize = 0;
            let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
            v___x_4205_ = 0usize;
            v___x_4206_ = lean_usize_of_nat(v___x_4197_);
            v___x_4207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_4190_, v___x_4205_, v___x_4206_, v___x_4196_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
            return v___x_4207_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(
    mut v___x_4208_: *mut LeanObject,
    mut v_decls_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
    mut v___y_4211_: *mut LeanObject,
    mut v___y_4212_: *mut LeanObject,
    mut v___y_4213_: *mut LeanObject,
    mut v___y_4214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4215_: *mut LeanObject = core::ptr::null_mut();
    v_res_4215_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(
        v___x_4208_,
        v_decls_4209_,
        v___y_4210_,
        v___y_4211_,
        v___y_4212_,
        v___y_4213_,
    );
    lean_dec(v___y_4213_);
    lean_dec_ref(v___y_4212_);
    lean_dec(v___y_4211_);
    lean_dec_ref(v___y_4210_);
    lean_dec_ref(v_decls_4209_);
    lean_dec(v___x_4208_);
    return v_res_4215_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    v___x_4278_ = lean_unsigned_to_nat(2803462840);
    v___x_4279_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
    v___x_4280_ = l_Lean_Name_num___override(v___x_4279_, v___x_4278_);
    return v___x_4280_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    v___x_4282_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
    v___x_4283_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4284_ = l_Lean_Name_str___override(v___x_4283_, v___x_4282_);
    return v___x_4284_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    v___x_4286_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
    v___x_4287_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4288_ = l_Lean_Name_str___override(v___x_4287_, v___x_4286_);
    return v___x_4288_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    v___x_4289_ = lean_unsigned_to_nat(2);
    v___x_4290_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4291_ = l_Lean_Name_num___override(v___x_4290_, v___x_4289_);
    return v___x_4291_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: u8 = 0;
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    v___x_4293_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
    v___x_4294_ = 1;
    v___x_4295_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4296_ = l_Lean_registerTraceClass(v___x_4293_, v___x_4294_, v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(
    mut v_a_4297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4298_: *mut LeanObject = core::ptr::null_mut();
    v_res_4298_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
    return v_res_4298_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ReduceArity(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ReduceArity(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ReduceArity(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
}
