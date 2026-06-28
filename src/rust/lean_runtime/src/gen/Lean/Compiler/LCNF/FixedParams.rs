// Lean compiler output
// Module: Lean.Compiler.LCNF.FixedParams
// Imports: Lean.Compiler.LCNF.Basic
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, l_Lean_Compiler_LCNF_instBEqArg_beq___redArg,
    runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint64,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static mut l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7_value: LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10_value)
        as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__1_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0: u64 = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx(
    mut v_x_1261_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1261_) {
        0 => {
            let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
            v___x_1262_ = lean_unsigned_to_nat(0);
            return v___x_1262_;
        }
        1 => {
            let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
            v___x_1263_ = lean_unsigned_to_nat(1);
            return v___x_1263_;
        }
        _ => {
            let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
            v___x_1264_ = lean_unsigned_to_nat(2);
            return v___x_1264_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx___boxed(
    mut v_x_1265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1266_: *mut LeanObject = core::ptr::null_mut();
    v_res_1266_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorIdx(v_x_1265_);
    lean_dec(v_x_1265_);
    return v_res_1266_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(
    mut v_t_1267_: *mut LeanObject,
    mut v_k_1268_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1267_) == 2 {
        let mut v_i_1269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
        v_i_1269_ = lean_ctor_get(v_t_1267_, 0);
        lean_inc(v_i_1269_);
        lean_dec_ref_known(v_t_1267_, 1);
        v___x_1270_ = lean_apply_1(v_k_1268_, v_i_1269_);
        return v___x_1270_;
    } else {
        lean_dec(v_t_1267_);
        return v_k_1268_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim(
    mut v_motive_1271_: *mut LeanObject,
    mut v_ctorIdx_1272_: *mut LeanObject,
    mut v_t_1273_: *mut LeanObject,
    mut v_h_1274_: *mut LeanObject,
    mut v_k_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_1273_, v_k_1275_);
    return v___x_1276_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___boxed(
    mut v_motive_1277_: *mut LeanObject,
    mut v_ctorIdx_1278_: *mut LeanObject,
    mut v_t_1279_: *mut LeanObject,
    mut v_h_1280_: *mut LeanObject,
    mut v_k_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1282_: *mut LeanObject = core::ptr::null_mut();
    v_res_1282_ = l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim(
        v_motive_1277_,
        v_ctorIdx_1278_,
        v_t_1279_,
        v_h_1280_,
        v_k_1281_,
    );
    lean_dec(v_ctorIdx_1278_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim___redArg(
    mut v_t_1283_: *mut LeanObject,
    mut v_top_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ =
        l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_1283_, v_top_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_top_elim(
    mut v_motive_1286_: *mut LeanObject,
    mut v_t_1287_: *mut LeanObject,
    mut v_h_1288_: *mut LeanObject,
    mut v_top_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    v___x_1290_ =
        l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_1287_, v_top_1289_);
    return v___x_1290_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim___redArg(
    mut v_t_1291_: *mut LeanObject,
    mut v_erased_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    v___x_1293_ =
        l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_1291_, v_erased_1292_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_erased_elim(
    mut v_motive_1294_: *mut LeanObject,
    mut v_t_1295_: *mut LeanObject,
    mut v_h_1296_: *mut LeanObject,
    mut v_erased_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ =
        l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_1295_, v_erased_1297_);
    return v___x_1298_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim___redArg(
    mut v_t_1299_: *mut LeanObject,
    mut v_val_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_1301_ =
        l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_1299_, v_val_1300_);
    return v___x_1301_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_AbsValue_val_elim(
    mut v_motive_1302_: *mut LeanObject,
    mut v_t_1303_: *mut LeanObject,
    mut v_h_1304_: *mut LeanObject,
    mut v_val_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    v___x_1306_ =
        l_Lean_Compiler_LCNF_FixedParams_AbsValue_ctorElim___redArg(v_t_1303_, v_val_1305_);
    return v___x_1306_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default()
-> *mut LeanObject {
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307_ = lean_box(0);
    return v___x_1307_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue() -> *mut LeanObject {
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    v___x_1308_ = lean_box(0);
    return v___x_1308_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(
    mut v_x_1309_: *mut LeanObject,
    mut v_x_1310_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_1309_) {
        0 => {
            if lean_obj_tag(v_x_1310_) == 0 {
                let mut v___x_1311_: u8 = 0;
                v___x_1311_ = 1;
                return v___x_1311_;
            } else {
                let mut v___x_1312_: u8 = 0;
                v___x_1312_ = 0;
                return v___x_1312_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_1310_) == 1 {
                let mut v___x_1313_: u8 = 0;
                v___x_1313_ = 1;
                return v___x_1313_;
            } else {
                let mut v___x_1314_: u8 = 0;
                v___x_1314_ = 0;
                return v___x_1314_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_1310_) == 2 {
                let mut v_i_1315_: *mut LeanObject = core::ptr::null_mut();
                let mut v_i_1316_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1317_: u8 = 0;
                v_i_1315_ = lean_ctor_get(v_x_1309_, 0);
                v_i_1316_ = lean_ctor_get(v_x_1310_, 0);
                v___x_1317_ = lean_nat_dec_eq(v_i_1315_, v_i_1316_);
                return v___x_1317_;
            } else {
                let mut v___x_1318_: u8 = 0;
                v___x_1318_ = 0;
                return v___x_1318_;
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq___boxed(
    mut v_x_1319_: *mut LeanObject,
    mut v_x_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1321_: u8 = 0;
    let mut v_r_1322_: *mut LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(v_x_1319_, v_x_1320_);
    lean_dec(v_x_1320_);
    lean_dec(v_x_1319_);
    v_r_1322_ = lean_box((v_res_1321_) as usize);
    return v_r_1322_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(
    mut v_x_1325_: *mut LeanObject,
) -> u64 {
    match lean_obj_tag(v_x_1325_) {
        0 => {
            let mut v___x_1326_: u64 = 0;
            v___x_1326_ = 0u64;
            return v___x_1326_;
        }
        1 => {
            let mut v___x_1327_: u64 = 0;
            v___x_1327_ = 1u64;
            return v___x_1327_;
        }
        _ => {
            let mut v_i_1328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1329_: u64 = 0;
            let mut v___x_1330_: u64 = 0;
            let mut v___x_1331_: u64 = 0;
            v_i_1328_ = lean_ctor_get(v_x_1325_, 0);
            v___x_1329_ = 2u64;
            v___x_1330_ = lean_uint64_of_nat(v_i_1328_);
            v___x_1331_ = lean_uint64_mix_hash(v___x_1329_, v___x_1330_);
            return v___x_1331_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash___boxed(
    mut v_x_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1333_: u64 = 0;
    let mut v_r_1334_: *mut LeanObject = core::ptr::null_mut();
    v_res_1333_ = l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v_x_1332_);
    lean_dec(v_x_1332_);
    v_r_1334_ = lean_box_uint64(v_res_1333_);
    return v_r_1334_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(mut v_x_1337_: u8) -> u8 {
    let mut v___x_1338_: u8 = 0;
    v___x_1338_ = 0;
    return v___x_1338_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0___boxed(
    mut v_x_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_273__boxed_1340_: u8 = 0;
    let mut v_res_1341_: u8 = 0;
    let mut v_r_1342_: *mut LeanObject = core::ptr::null_mut();
    v_x_273__boxed_1340_ = (lean_unbox(v_x_1339_) as u8);
    v_res_1341_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___lam__0(v_x_273__boxed_1340_);
    v_r_1342_ = lean_box((v_res_1341_) as usize);
    return v_r_1342_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_abort___redArg(
    mut v_a_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_visited_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixed_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1368_: u8 = 0;
    let mut v___f_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1371_: usize = 0;
    let mut v___x_1372_: usize = 0;
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_1364_ = lean_ctor_get(v_a_1363_, 0);
                v_fixed_1365_ = lean_ctor_get(v_a_1363_, 1);
                v_isSharedCheck_1379_ = (!lean_is_exclusive(v_a_1363_)) as u8;
                if v_isSharedCheck_1379_ == 0 {
                    v___x_1367_ = v_a_1363_;
                    v_isShared_1368_ = v_isSharedCheck_1379_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fixed_1365_);
                    lean_inc(v_visited_1364_);
                    lean_dec(v_a_1363_);
                    v___x_1367_ = lean_box(0);
                    v_isShared_1368_ = v_isSharedCheck_1379_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1369_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0;
                v___x_1370_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10;
                v_sz_1371_ = lean_array_size(v_fixed_1365_);
                v___x_1372_ = 0usize;
                v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_1370_,
                    v___f_1369_,
                    v_sz_1371_,
                    v___x_1372_,
                    v_fixed_1365_,
                );
                if v_isShared_1368_ == 0 {
                    lean_ctor_set(v___x_1367_, 1, v___x_1373_);
                    v___x_1375_ = v___x_1367_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_visited_1364_);
                    lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1373_);
                    v___x_1375_ = v_reuseFailAlloc_1378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1376_ = lean_box(0);
                v___x_1377_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1377_, 0, v___x_1376_);
                lean_ctor_set(v___x_1377_, 1, v___x_1375_);
                return v___x_1377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_abort(
    mut v_00_u03b1_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_a_1382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_visited_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixed_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1387_: u8 = 0;
    let mut v___f_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_visited_1383_ = lean_ctor_get(v_a_1382_, 0);
                v_fixed_1384_ = lean_ctor_get(v_a_1382_, 1);
                v_isSharedCheck_1398_ = (!lean_is_exclusive(v_a_1382_)) as u8;
                if v_isSharedCheck_1398_ == 0 {
                    v___x_1386_ = v_a_1382_;
                    v_isShared_1387_ = v_isSharedCheck_1398_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_fixed_1384_);
                    lean_inc(v_visited_1383_);
                    lean_dec(v_a_1382_);
                    v___x_1386_ = lean_box(0);
                    v_isShared_1387_ = v_isSharedCheck_1398_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1388_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__0;
                v___x_1389_ = l_Lean_Compiler_LCNF_FixedParams_abort___redArg___closed__10;
                v_sz_1390_ = lean_array_size(v_fixed_1384_);
                v___x_1391_ = 0usize;
                v___x_1392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_1389_,
                    v___f_1388_,
                    v_sz_1390_,
                    v___x_1391_,
                    v_fixed_1384_,
                );
                if v_isShared_1387_ == 0 {
                    lean_ctor_set(v___x_1386_, 1, v___x_1392_);
                    v___x_1394_ = v___x_1386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_visited_1383_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1392_);
                    v___x_1394_ = v_reuseFailAlloc_1397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1395_ = lean_box(0);
                v___x_1396_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1396_, 0, v___x_1395_);
                lean_ctor_set(v___x_1396_, 1, v___x_1394_);
                return v___x_1396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_abort___boxed(
    mut v_00_u03b1_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1402_: *mut LeanObject = core::ptr::null_mut();
    v_res_1402_ = l_Lean_Compiler_LCNF_FixedParams_abort(v_00_u03b1_1399_, v_a_1400_, v_a_1401_);
    lean_dec_ref(v_a_1400_);
    return v_res_1402_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(
    mut v_t_1403_: *mut LeanObject,
    mut v_k_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1403_) == 0 {
                    v_k_1405_ = lean_ctor_get(v_t_1403_, 1);
                    v_v_1406_ = lean_ctor_get(v_t_1403_, 2);
                    v_l_1407_ = lean_ctor_get(v_t_1403_, 3);
                    v_r_1408_ = lean_ctor_get(v_t_1403_, 4);
                    v___x_1409_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1404_, v_k_1405_);
                    match v___x_1409_ {
                        0 => {
                            v_t_1403_ = v_l_1407_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_1406_);
                            v___x_1411_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1411_, 0, v_v_1406_);
                            return v___x_1411_;
                        }
                        _ => {
                            v_t_1403_ = v_r_1408_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1413_ = lean_box(0);
                    return v___x_1413_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg___boxed(
    mut v_t_1414_: *mut LeanObject,
    mut v_k_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1416_: *mut LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_1414_, v_k_1415_);
    lean_dec(v_k_1415_);
    lean_dec(v_t_1414_);
    return v_res_1416_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalFVar(
    mut v_fvarId_1417_: *mut LeanObject,
    mut v_a_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_assignment_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v_assignment_1420_ = lean_ctor_get(v_a_1418_, 2);
    v___x_1421_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_1420_, v_fvarId_1417_);
    if lean_obj_tag(v___x_1421_) == 1 {
        let mut v_val_1422_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
        v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
        lean_inc(v_val_1422_);
        lean_dec_ref_known(v___x_1421_, 1);
        v___x_1423_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1423_, 0, v_val_1422_);
        lean_ctor_set(v___x_1423_, 1, v_a_1419_);
        return v___x_1423_;
    } else {
        let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1421_);
        v___x_1424_ = lean_box(0);
        v___x_1425_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1425_, 0, v___x_1424_);
        lean_ctor_set(v___x_1425_, 1, v_a_1419_);
        return v___x_1425_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalFVar___boxed(
    mut v_fvarId_1426_: *mut LeanObject,
    mut v_a_1427_: *mut LeanObject,
    mut v_a_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_1426_, v_a_1427_, v_a_1428_);
    lean_dec_ref(v_a_1427_);
    lean_dec(v_fvarId_1426_);
    return v_res_1429_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(
    mut v_00_u03b4_1430_: *mut LeanObject,
    mut v_t_1431_: *mut LeanObject,
    mut v_k_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_t_1431_, v_k_1432_);
    return v___x_1433_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___boxed(
    mut v_00_u03b4_1434_: *mut LeanObject,
    mut v_t_1435_: *mut LeanObject,
    mut v_k_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1437_: *mut LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0(v_00_u03b4_1434_, v_t_1435_, v_k_1436_);
    lean_dec(v_k_1436_);
    lean_dec(v_t_1435_);
    return v_res_1437_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalArg(
    mut v_arg_1438_: *mut LeanObject,
    mut v_a_1439_: *mut LeanObject,
    mut v_a_1440_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_arg_1438_) {
        0 => {
            let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
            v___x_1441_ = lean_box(1);
            v___x_1442_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1442_, 0, v___x_1441_);
            lean_ctor_set(v___x_1442_, 1, v_a_1440_);
            return v___x_1442_;
        }
        1 => {
            let mut v_fvarId_1443_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
            v_fvarId_1443_ = lean_ctor_get(v_arg_1438_, 0);
            v___x_1444_ =
                l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_1443_, v_a_1439_, v_a_1440_);
            return v___x_1444_;
        }
        _ => {
            let mut v_expr_1445_: *mut LeanObject = core::ptr::null_mut();
            v_expr_1445_ = lean_ctor_get(v_arg_1438_, 0);
            if lean_obj_tag(v_expr_1445_) == 1 {
                let mut v_fvarId_1446_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
                v_fvarId_1446_ = lean_ctor_get(v_expr_1445_, 0);
                v___x_1447_ =
                    l_Lean_Compiler_LCNF_FixedParams_evalFVar(v_fvarId_1446_, v_a_1439_, v_a_1440_);
                return v___x_1447_;
            } else {
                let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
                v___x_1448_ = lean_box(0);
                v___x_1449_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1449_, 0, v___x_1448_);
                lean_ctor_set(v___x_1449_, 1, v_a_1440_);
                return v___x_1449_;
            }
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalArg___boxed(
    mut v_arg_1450_: *mut LeanObject,
    mut v_a_1451_: *mut LeanObject,
    mut v_a_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1453_: *mut LeanObject = core::ptr::null_mut();
    v_res_1453_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(v_arg_1450_, v_a_1451_, v_a_1452_);
    lean_dec_ref(v_a_1451_);
    lean_dec(v_arg_1450_);
    return v_res_1453_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(
    mut v_declName_1454_: *mut LeanObject,
    mut v_as_1455_: *mut LeanObject,
    mut v_i_1456_: usize,
    mut v_stop_1457_: usize,
) -> u8 {
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: u8 = 0;
    let mut v___x_1463_: usize = 0;
    let mut v___x_1464_: usize = 0;
    let mut v___x_1466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1458_ = lean_usize_dec_eq(v_i_1456_, v_stop_1457_);
                if v___x_1458_ == 0 {
                    v___x_1459_ = lean_array_uget_borrowed(v_as_1455_, v_i_1456_);
                    v_toSignature_1460_ = lean_ctor_get(v___x_1459_, 0);
                    v_name_1461_ = lean_ctor_get(v_toSignature_1460_, 0);
                    v___x_1462_ = lean_name_eq(v_name_1461_, v_declName_1454_);
                    if v___x_1462_ == 0 {
                        v___x_1463_ = 1usize;
                        v___x_1464_ = lean_usize_add(v_i_1456_, v___x_1463_);
                        v_i_1456_ = v___x_1464_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1462_;
                    }
                } else {
                    v___x_1466_ = 0;
                    return v___x_1466_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0___boxed(
    mut v_declName_1467_: *mut LeanObject,
    mut v_as_1468_: *mut LeanObject,
    mut v_i_1469_: *mut LeanObject,
    mut v_stop_1470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1471_: usize = 0;
    let mut v_stop_boxed_1472_: usize = 0;
    let mut v_res_1473_: u8 = 0;
    let mut v_r_1474_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1471_ = lean_unbox_usize(v_i_1469_);
    lean_dec(v_i_1469_);
    v_stop_boxed_1472_ = lean_unbox_usize(v_stop_1470_);
    lean_dec(v_stop_1470_);
    v_res_1473_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_1467_, v_as_1468_, v_i_boxed_1471_, v_stop_boxed_1472_);
    lean_dec_ref(v_as_1468_);
    lean_dec(v_declName_1467_);
    v_r_1474_ = lean_box((v_res_1473_) as usize);
    return v_r_1474_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(
    mut v_declName_1475_: *mut LeanObject,
    mut v_a_1476_: *mut LeanObject,
    mut v_a_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: u8 = 0;
    v_decls_1478_ = lean_ctor_get(v_a_1476_, 0);
    v___x_1479_ = lean_unsigned_to_nat(0);
    v___x_1480_ = lean_array_get_size(v_decls_1478_);
    v___x_1481_ = lean_nat_dec_lt(v___x_1479_, v___x_1480_);
    if v___x_1481_ == 0 {
        let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
        v___x_1482_ = lean_box((v___x_1481_) as usize);
        v___x_1483_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1483_, 0, v___x_1482_);
        lean_ctor_set(v___x_1483_, 1, v_a_1477_);
        return v___x_1483_;
    } else {
        if v___x_1481_ == 0 {
            let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
            v___x_1484_ = lean_box((v___x_1481_) as usize);
            v___x_1485_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1485_, 0, v___x_1484_);
            lean_ctor_set(v___x_1485_, 1, v_a_1477_);
            return v___x_1485_;
        } else {
            let mut v___x_1486_: usize = 0;
            let mut v___x_1487_: usize = 0;
            let mut v___x_1488_: u8 = 0;
            let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
            v___x_1486_ = 0usize;
            v___x_1487_ = lean_usize_of_nat(v___x_1480_);
            v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_FixedParams_inMutualBlock_spec__0(v_declName_1475_, v_decls_1478_, v___x_1486_, v___x_1487_);
            v___x_1489_ = lean_box((v___x_1488_) as usize);
            v___x_1490_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_1490_, 0, v___x_1489_);
            lean_ctor_set(v___x_1490_, 1, v_a_1477_);
            return v___x_1490_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_inMutualBlock___boxed(
    mut v_declName_1491_: *mut LeanObject,
    mut v_a_1492_: *mut LeanObject,
    mut v_a_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1494_: *mut LeanObject = core::ptr::null_mut();
    v_res_1494_ =
        l_Lean_Compiler_LCNF_FixedParams_inMutualBlock(v_declName_1491_, v_a_1492_, v_a_1493_);
    lean_dec_ref(v_a_1492_);
    lean_dec(v_declName_1491_);
    return v_res_1494_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(
    mut v_as_1495_: *mut LeanObject,
    mut v_sz_1496_: usize,
    mut v_i_1497_: usize,
    mut v_b_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1499_: u8 = 0;
    let mut v_snd_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v_array_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v_a_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: usize = 0;
    let mut v___x_1526_: usize = 0;
    let mut v_reuseFailAlloc_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1530_: u8 = 0;
    let mut v_unused_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1499_ = lean_usize_dec_lt(v_i_1497_, v_sz_1496_);
                if v___x_1499_ == 0 {
                    return v_b_1498_;
                } else {
                    v_snd_1500_ = lean_ctor_get(v_b_1498_, 1);
                    v_fst_1501_ = lean_ctor_get(v_b_1498_, 0);
                    v_isSharedCheck_1534_ = (!lean_is_exclusive(v_b_1498_)) as u8;
                    if v_isSharedCheck_1534_ == 0 {
                        v___x_1503_ = v_b_1498_;
                        v_isShared_1504_ = v_isSharedCheck_1534_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1500_);
                        lean_inc(v_fst_1501_);
                        lean_dec(v_b_1498_);
                        v___x_1503_ = lean_box(0);
                        v_isShared_1504_ = v_isSharedCheck_1534_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_1505_ = lean_ctor_get(v_snd_1500_, 0);
                v_start_1506_ = lean_ctor_get(v_snd_1500_, 1);
                v_stop_1507_ = lean_ctor_get(v_snd_1500_, 2);
                v___x_1508_ = lean_nat_dec_lt(v_start_1506_, v_stop_1507_);
                if v___x_1508_ == 0 {
                    if v_isShared_1504_ == 0 {
                        v___x_1510_ = v___x_1503_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_fst_1501_);
                        lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_snd_1500_);
                        v___x_1510_ = v_reuseFailAlloc_1511_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_1507_);
                    lean_inc(v_start_1506_);
                    lean_inc_ref(v_array_1505_);
                    v_isSharedCheck_1530_ = (!lean_is_exclusive(v_snd_1500_)) as u8;
                    if v_isSharedCheck_1530_ == 0 {
                        v_unused_1531_ = lean_ctor_get(v_snd_1500_, 2);
                        lean_dec(v_unused_1531_);
                        v_unused_1532_ = lean_ctor_get(v_snd_1500_, 1);
                        lean_dec(v_unused_1532_);
                        v_unused_1533_ = lean_ctor_get(v_snd_1500_, 0);
                        lean_dec(v_unused_1533_);
                        v___x_1513_ = v_snd_1500_;
                        v_isShared_1514_ = v_isSharedCheck_1530_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_snd_1500_);
                        v___x_1513_ = lean_box(0);
                        v_isShared_1514_ = v_isSharedCheck_1530_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1510_;
            }
            3 => {
                v_a_1515_ = lean_array_uget_borrowed(v_as_1495_, v_i_1497_);
                v_fvarId_1516_ = lean_ctor_get(v_a_1515_, 0);
                v___x_1517_ = lean_array_fget(v_array_1505_, v_start_1506_);
                v___x_1518_ = lean_unsigned_to_nat(1);
                v___x_1519_ = lean_nat_add(v_start_1506_, v___x_1518_);
                lean_dec(v_start_1506_);
                if v_isShared_1514_ == 0 {
                    lean_ctor_set(v___x_1513_, 1, v___x_1519_);
                    v___x_1521_ = v___x_1513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_array_1505_);
                    lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1519_);
                    lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_stop_1507_);
                    v___x_1521_ = v_reuseFailAlloc_1529_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_fvarId_1516_);
                v___x_1522_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1516_, v___x_1517_, v_fst_1501_);
                if v_isShared_1504_ == 0 {
                    lean_ctor_set(v___x_1503_, 1, v___x_1521_);
                    lean_ctor_set(v___x_1503_, 0, v___x_1522_);
                    v___x_1524_ = v___x_1503_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1522_);
                    lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1521_);
                    v___x_1524_ = v_reuseFailAlloc_1528_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1525_ = 1usize;
                v___x_1526_ = lean_usize_add(v_i_1497_, v___x_1525_);
                v_i_1497_ = v___x_1526_;
                v_b_1498_ = v___x_1524_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0___boxed(
    mut v_as_1535_: *mut LeanObject,
    mut v_sz_1536_: *mut LeanObject,
    mut v_i_1537_: *mut LeanObject,
    mut v_b_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1539_: usize = 0;
    let mut v_i_boxed_1540_: usize = 0;
    let mut v_res_1541_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1539_ = lean_unbox_usize(v_sz_1536_);
    lean_dec(v_sz_1536_);
    v_i_boxed_1540_ = lean_unbox_usize(v_i_1537_);
    lean_dec(v_i_1537_);
    v_res_1541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_as_1535_, v_sz_boxed_1539_, v_i_boxed_1540_, v_b_1538_);
    lean_dec_ref(v_as_1535_);
    return v_res_1541_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_mkAssignment(
    mut v_decl_1542_: *mut LeanObject,
    mut v_values_1543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1551_: usize = 0;
    let mut v___x_1552_: usize = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1554_: *mut LeanObject = core::ptr::null_mut();
    v_toSignature_1544_ = lean_ctor_get(v_decl_1542_, 0);
    v_params_1545_ = lean_ctor_get(v_toSignature_1544_, 3);
    v___x_1546_ = lean_array_get_size(v_values_1543_);
    v_assignment_1547_ = lean_box(1);
    v___x_1548_ = lean_unsigned_to_nat(0);
    v___x_1549_ = l_Array_toSubarray___redArg(v_values_1543_, v___x_1548_, v___x_1546_);
    v___x_1550_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1550_, 0, v_assignment_1547_);
    lean_ctor_set(v___x_1550_, 1, v___x_1549_);
    v_sz_1551_ = lean_array_size(v_params_1545_);
    v___x_1552_ = 0usize;
    v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_mkAssignment_spec__0(v_params_1545_, v_sz_1551_, v___x_1552_, v___x_1550_);
    v_fst_1554_ = lean_ctor_get(v___x_1553_, 0);
    lean_inc(v_fst_1554_);
    lean_dec_ref(v___x_1553_);
    return v_fst_1554_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_mkAssignment___boxed(
    mut v_decl_1555_: *mut LeanObject,
    mut v_values_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1557_: *mut LeanObject = core::ptr::null_mut();
    v_res_1557_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_decl_1555_, v_values_1556_);
    lean_dec_ref(v_decl_1555_);
    return v_res_1557_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(
    mut v_params_1566_: *mut LeanObject,
    mut v_args_1567_: *mut LeanObject,
    mut v___x_1568_: u8,
    mut v_range_1569_: *mut LeanObject,
    mut v_b_1570_: *mut LeanObject,
    mut v_i_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stop_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_step_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_1573_ = lean_ctor_get(v_range_1569_, 1);
                v_step_1574_ = lean_ctor_get(v_range_1569_, 2);
                v___x_1575_ = lean_nat_dec_lt(v_i_1571_, v_stop_1573_);
                if v___x_1575_ == 0 {
                    lean_dec(v_i_1571_);
                    v___x_1576_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1576_, 0, v_b_1570_);
                    lean_ctor_set(v___x_1576_, 1, v___y_1572_);
                    return v___x_1576_;
                } else {
                    lean_dec_ref(v_b_1570_);
                    v___x_1577_ = lean_array_fget_borrowed(v_params_1566_, v_i_1571_);
                    v_fvarId_1578_ = lean_ctor_get(v___x_1577_, 0);
                    v___x_1579_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0;
                    v___x_1584_ = lean_box(0);
                    v___x_1585_ = lean_array_get_borrowed(v___x_1584_, v_args_1567_, v_i_1571_);
                    lean_inc(v_fvarId_1578_);
                    v___x_1586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1586_, 0, v_fvarId_1578_);
                    v___x_1587_ =
                        l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(v___x_1585_, v___x_1586_);
                    lean_dec_ref_known(v___x_1586_, 1);
                    if v___x_1587_ == 0 {
                        if v___x_1568_ == 0 {
                            v_a_1581_ = v___y_1572_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1588_ = l_Lean_Compiler_LCNF_instBEqArg_beq___redArg(
                                v___x_1585_,
                                v___x_1584_,
                            );
                            if v___x_1588_ == 0 {
                                lean_dec(v_i_1571_);
                                v___x_1589_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__2;
                                v___x_1590_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_1590_, 0, v___x_1589_);
                                lean_ctor_set(v___x_1590_, 1, v___y_1572_);
                                return v___x_1590_;
                            } else {
                                v_a_1581_ = v___y_1572_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_1581_ = v___y_1572_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1582_ = lean_nat_add(v_i_1571_, v_step_1574_);
                lean_dec(v_i_1571_);
                v_b_1570_ = v___x_1579_;
                v_i_1571_ = v___x_1582_;
                v___y_1572_ = v_a_1581_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___boxed(
    mut v_params_1591_: *mut LeanObject,
    mut v_args_1592_: *mut LeanObject,
    mut v___x_1593_: *mut LeanObject,
    mut v_range_1594_: *mut LeanObject,
    mut v_b_1595_: *mut LeanObject,
    mut v_i_1596_: *mut LeanObject,
    mut v___y_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3934__boxed_1598_: u8 = 0;
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v___x_3934__boxed_1598_ = (lean_unbox(v___x_1593_) as u8);
    v_res_1599_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_1591_, v_args_1592_, v___x_3934__boxed_1598_, v_range_1594_, v_b_1595_, v_i_1596_, v___y_1597_);
    lean_dec_ref(v_range_1594_);
    lean_dec_ref(v_args_1592_);
    lean_dec_ref(v_params_1591_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(
    mut v_decl_1600_: *mut LeanObject,
    mut v_a_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v_i_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1652_: u8 = 0;
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v_unused_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1664_: u8 = 0;
    let mut v_val_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_unused_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_1611_ = lean_ctor_get(v_decl_1600_, 4);
                lean_inc_ref(v_value_1611_);
                if lean_obj_tag(v_value_1611_) == 0 {
                    v_decl_1612_ = lean_ctor_get(v_value_1611_, 0);
                    lean_inc_ref(v_decl_1612_);
                    v_value_1613_ = lean_ctor_get(v_decl_1612_, 3);
                    lean_inc(v_value_1613_);
                    if lean_obj_tag(v_value_1613_) == 4 {
                        v_params_1614_ = lean_ctor_get(v_decl_1600_, 2);
                        lean_inc_ref(v_params_1614_);
                        lean_dec_ref(v_decl_1600_);
                        v_k_1615_ = lean_ctor_get(v_value_1611_, 1);
                        lean_inc_ref(v_k_1615_);
                        lean_dec_ref_known(v_value_1611_, 2);
                        v_fvarId_1616_ = lean_ctor_get(v_decl_1612_, 0);
                        lean_inc(v_fvarId_1616_);
                        lean_dec_ref(v_decl_1612_);
                        v_fvarId_1617_ = lean_ctor_get(v_value_1613_, 0);
                        v_args_1618_ = lean_ctor_get(v_value_1613_, 1);
                        v_isSharedCheck_1676_ = (!lean_is_exclusive(v_value_1613_)) as u8;
                        if v_isSharedCheck_1676_ == 0 {
                            v___x_1620_ = v_value_1613_;
                            v_isShared_1621_ = v_isSharedCheck_1676_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_args_1618_);
                            lean_inc(v_fvarId_1617_);
                            lean_dec(v_value_1613_);
                            v___x_1620_ = lean_box(0);
                            v_isShared_1621_ = v_isSharedCheck_1676_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_value_1613_);
                        lean_dec_ref(v_decl_1612_);
                        lean_dec_ref_known(v_value_1611_, 2);
                        lean_dec_ref(v_decl_1600_);
                        v___y_1604_ = v_a_1602_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_1611_);
                    lean_dec_ref(v_decl_1600_);
                    v___y_1604_ = v_a_1602_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1605_ = lean_box(0);
                v___x_1606_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1606_, 0, v___x_1605_);
                lean_ctor_set(v___x_1606_, 1, v___y_1604_);
                return v___x_1606_;
            }
            2 => {
                v___x_1609_ = lean_box(0);
                v___x_1610_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1610_, 0, v___x_1609_);
                lean_ctor_set(v___x_1610_, 1, v___y_1608_);
                return v___x_1610_;
            }
            3 => {
                v___x_1622_ = lean_array_get_size(v_args_1618_);
                v___x_1623_ = lean_array_get_size(v_params_1614_);
                v___x_1624_ = lean_nat_dec_eq(v___x_1622_, v___x_1623_);
                if v___x_1624_ == 0 {
                    lean_dec_ref(v_args_1618_);
                    lean_dec(v_fvarId_1617_);
                    lean_dec(v_fvarId_1616_);
                    lean_dec_ref(v_k_1615_);
                    lean_dec_ref(v_params_1614_);
                    v___x_1625_ = lean_box(0);
                    if v_isShared_1621_ == 0 {
                        lean_ctor_set_tag(v___x_1620_, 0);
                        lean_ctor_set(v___x_1620_, 1, v_a_1602_);
                        lean_ctor_set(v___x_1620_, 0, v___x_1625_);
                        v___x_1627_ = v___x_1620_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
                        lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_a_1602_);
                        v___x_1627_ = v_reuseFailAlloc_1628_;
                        state = 4;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_k_1615_) == 5 {
                        v_fvarId_1629_ = lean_ctor_get(v_k_1615_, 0);
                        lean_inc(v_fvarId_1629_);
                        lean_dec_ref_known(v_k_1615_, 1);
                        v___x_1630_ = l_Lean_instBEqFVarId_beq(v_fvarId_1629_, v_fvarId_1616_);
                        lean_dec(v_fvarId_1616_);
                        lean_dec(v_fvarId_1629_);
                        if v___x_1630_ == 0 {
                            lean_dec_ref(v_args_1618_);
                            lean_dec(v_fvarId_1617_);
                            lean_dec_ref(v_params_1614_);
                            v___x_1631_ = lean_box(0);
                            if v_isShared_1621_ == 0 {
                                lean_ctor_set_tag(v___x_1620_, 0);
                                lean_ctor_set(v___x_1620_, 1, v_a_1602_);
                                lean_ctor_set(v___x_1620_, 0, v___x_1631_);
                                v___x_1633_ = v___x_1620_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
                                lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_a_1602_);
                                v___x_1633_ = v_reuseFailAlloc_1634_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1620_);
                            v_assignment_1635_ = lean_ctor_get(v_a_1601_, 2);
                            v___x_1636_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_FixedParams_evalFVar_spec__0___redArg(v_assignment_1635_, v_fvarId_1617_);
                            lean_dec(v_fvarId_1617_);
                            if lean_obj_tag(v___x_1636_) == 1 {
                                v_val_1637_ = lean_ctor_get(v___x_1636_, 0);
                                v_isSharedCheck_1671_ = (!lean_is_exclusive(v___x_1636_)) as u8;
                                if v_isSharedCheck_1671_ == 0 {
                                    v___x_1639_ = v___x_1636_;
                                    v_isShared_1640_ = v_isSharedCheck_1671_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_val_1637_);
                                    lean_dec(v___x_1636_);
                                    v___x_1639_ = lean_box(0);
                                    v_isShared_1640_ = v_isSharedCheck_1671_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1636_);
                                lean_dec_ref(v_args_1618_);
                                lean_dec_ref(v_params_1614_);
                                v___y_1608_ = v_a_1602_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_args_1618_);
                        lean_dec(v_fvarId_1617_);
                        lean_dec(v_fvarId_1616_);
                        lean_dec_ref(v_k_1615_);
                        lean_dec_ref(v_params_1614_);
                        v___x_1672_ = lean_box(0);
                        if v_isShared_1621_ == 0 {
                            lean_ctor_set_tag(v___x_1620_, 0);
                            lean_ctor_set(v___x_1620_, 1, v_a_1602_);
                            lean_ctor_set(v___x_1620_, 0, v___x_1672_);
                            v___x_1674_ = v___x_1620_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
                            lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_a_1602_);
                            v___x_1674_ = v_reuseFailAlloc_1675_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_1627_;
            }
            5 => {
                return v___x_1633_;
            }
            6 => {
                if lean_obj_tag(v_val_1637_) == 2 {
                    v_i_1641_ = lean_ctor_get(v_val_1637_, 0);
                    lean_inc(v_i_1641_);
                    lean_dec_ref_known(v_val_1637_, 1);
                    v___x_1642_ = lean_unsigned_to_nat(0);
                    v___x_1643_ = lean_unsigned_to_nat(1);
                    v___x_1644_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1644_, 0, v___x_1642_);
                    lean_ctor_set(v___x_1644_, 1, v___x_1623_);
                    lean_ctor_set(v___x_1644_, 2, v___x_1643_);
                    v___x_1645_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg___closed__0;
                    v___x_1646_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_1614_, v_args_1618_, v___x_1630_, v___x_1644_, v___x_1645_, v___x_1642_, v_a_1602_);
                    lean_dec_ref_known(v___x_1644_, 3);
                    lean_dec_ref(v_args_1618_);
                    lean_dec_ref(v_params_1614_);
                    v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
                    lean_inc(v_a_1647_);
                    v_fst_1648_ = lean_ctor_get(v_a_1647_, 0);
                    lean_inc(v_fst_1648_);
                    lean_dec(v_a_1647_);
                    if lean_obj_tag(v_fst_1648_) == 0 {
                        v_a_1649_ = lean_ctor_get(v___x_1646_, 1);
                        v_isSharedCheck_1659_ = (!lean_is_exclusive(v___x_1646_)) as u8;
                        if v_isSharedCheck_1659_ == 0 {
                            v_unused_1660_ = lean_ctor_get(v___x_1646_, 0);
                            lean_dec(v_unused_1660_);
                            v___x_1651_ = v___x_1646_;
                            v_isShared_1652_ = v_isSharedCheck_1659_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1649_);
                            lean_dec(v___x_1646_);
                            v___x_1651_ = lean_box(0);
                            v_isShared_1652_ = v_isSharedCheck_1659_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_1641_);
                        lean_del_object(v___x_1639_);
                        v_a_1661_ = lean_ctor_get(v___x_1646_, 1);
                        v_isSharedCheck_1669_ = (!lean_is_exclusive(v___x_1646_)) as u8;
                        if v_isSharedCheck_1669_ == 0 {
                            v_unused_1670_ = lean_ctor_get(v___x_1646_, 0);
                            lean_dec(v_unused_1670_);
                            v___x_1663_ = v___x_1646_;
                            v_isShared_1664_ = v_isSharedCheck_1669_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1661_);
                            lean_dec(v___x_1646_);
                            v___x_1663_ = lean_box(0);
                            v_isShared_1664_ = v_isSharedCheck_1669_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1639_);
                    lean_dec(v_val_1637_);
                    lean_dec_ref(v_args_1618_);
                    lean_dec_ref(v_params_1614_);
                    v___y_1608_ = v_a_1602_;
                    state = 2;
                    continue;
                }
            }
            7 => {
                if v_isShared_1640_ == 0 {
                    lean_ctor_set(v___x_1639_, 0, v_i_1641_);
                    v___x_1654_ = v___x_1639_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_i_1641_);
                    v___x_1654_ = v_reuseFailAlloc_1658_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1652_ == 0 {
                    lean_ctor_set(v___x_1651_, 0, v___x_1654_);
                    v___x_1656_ = v___x_1651_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
                    lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1649_);
                    v___x_1656_ = v_reuseFailAlloc_1657_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1656_;
            }
            10 => {
                v_val_1665_ = lean_ctor_get(v_fst_1648_, 0);
                lean_inc(v_val_1665_);
                lean_dec_ref_known(v_fst_1648_, 1);
                if v_isShared_1664_ == 0 {
                    lean_ctor_set(v___x_1663_, 0, v_val_1665_);
                    v___x_1667_ = v___x_1663_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_val_1665_);
                    lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_a_1661_);
                    v___x_1667_ = v_reuseFailAlloc_1668_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1667_;
            }
            12 => {
                return v___x_1674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f___boxed(
    mut v_decl_1677_: *mut LeanObject,
    mut v_a_1678_: *mut LeanObject,
    mut v_a_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1680_: *mut LeanObject = core::ptr::null_mut();
    v_res_1680_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(
        v_decl_1677_,
        v_a_1678_,
        v_a_1679_,
    );
    lean_dec_ref(v_a_1678_);
    return v_res_1680_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(
    mut v_params_1681_: *mut LeanObject,
    mut v_args_1682_: *mut LeanObject,
    mut v___x_1683_: u8,
    mut v_range_1684_: *mut LeanObject,
    mut v_b_1685_: *mut LeanObject,
    mut v_i_1686_: *mut LeanObject,
    mut v_hs_1687_: *mut LeanObject,
    mut v_hl_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___redArg(v_params_1681_, v_args_1682_, v___x_1683_, v_range_1684_, v_b_1685_, v_i_1686_, v___y_1690_);
    return v___x_1691_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0___boxed(
    mut v_params_1692_: *mut LeanObject,
    mut v_args_1693_: *mut LeanObject,
    mut v___x_1694_: *mut LeanObject,
    mut v_range_1695_: *mut LeanObject,
    mut v_b_1696_: *mut LeanObject,
    mut v_i_1697_: *mut LeanObject,
    mut v_hs_1698_: *mut LeanObject,
    mut v_hl_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4138__boxed_1702_: u8 = 0;
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v___x_4138__boxed_1702_ = (lean_unbox(v___x_1694_) as u8);
    v_res_1703_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f_spec__0(v_params_1692_, v_args_1693_, v___x_4138__boxed_1702_, v_range_1695_, v_b_1696_, v_i_1697_, v_hs_1698_, v_hl_1699_, v___y_1700_, v___y_1701_);
    lean_dec_ref(v___y_1700_);
    lean_dec_ref(v_range_1695_);
    lean_dec_ref(v_args_1693_);
    lean_dec_ref(v_params_1692_);
    return v_res_1703_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(
    mut v_upperBound_1704_: *mut LeanObject,
    mut v_args_1705_: *mut LeanObject,
    mut v_a_1706_: *mut LeanObject,
    mut v_b_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v_visited_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixed_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1725_: u8 = 0;
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1731_: u8 = 0;
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: u8 = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v_visited_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixed_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut v_a_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1755_: u8 = 0;
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1716_ = lean_nat_dec_lt(v_a_1706_, v_upperBound_1704_);
                if v___x_1716_ == 0 {
                    lean_dec(v_a_1706_);
                    v___x_1717_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1717_, 0, v_b_1707_);
                    lean_ctor_set(v___x_1717_, 1, v___y_1709_);
                    return v___x_1717_;
                } else {
                    v___x_1718_ = lean_box(0);
                    v___x_1719_ = lean_array_get_size(v_args_1705_);
                    v___x_1720_ = lean_nat_dec_lt(v_a_1706_, v___x_1719_);
                    if v___x_1720_ == 0 {
                        v_visited_1721_ = lean_ctor_get(v___y_1709_, 0);
                        v_fixed_1722_ = lean_ctor_get(v___y_1709_, 1);
                        v_isSharedCheck_1731_ = (!lean_is_exclusive(v___y_1709_)) as u8;
                        if v_isSharedCheck_1731_ == 0 {
                            v___x_1724_ = v___y_1709_;
                            v_isShared_1725_ = v_isSharedCheck_1731_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_fixed_1722_);
                            lean_inc(v_visited_1721_);
                            lean_dec(v___y_1709_);
                            v___x_1724_ = lean_box(0);
                            v_isShared_1725_ = v_isSharedCheck_1731_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1732_ = lean_array_fget_borrowed(v_args_1705_, v_a_1706_);
                        v___x_1733_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(
                            v___x_1732_,
                            v___y_1708_,
                            v___y_1709_,
                        );
                        if lean_obj_tag(v___x_1733_) == 0 {
                            v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
                            lean_inc(v_a_1734_);
                            v_a_1735_ = lean_ctor_get(v___x_1733_, 1);
                            lean_inc(v_a_1735_);
                            lean_dec_ref_known(v___x_1733_, 2);
                            lean_inc(v_a_1706_);
                            v___x_1736_ = lean_alloc_ctor(2, 1, (0) as u32);
                            lean_ctor_set(v___x_1736_, 0, v_a_1706_);
                            v___x_1737_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(
                                v_a_1734_,
                                v___x_1736_,
                            );
                            lean_dec_ref_known(v___x_1736_, 1);
                            if v___x_1737_ == 0 {
                                v___x_1738_ = lean_box(1);
                                v___x_1739_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(
                                    v_a_1734_,
                                    v___x_1738_,
                                );
                                lean_dec(v_a_1734_);
                                if v___x_1739_ == 0 {
                                    v_visited_1740_ = lean_ctor_get(v_a_1735_, 0);
                                    v_fixed_1741_ = lean_ctor_get(v_a_1735_, 1);
                                    v_isSharedCheck_1750_ = (!lean_is_exclusive(v_a_1735_)) as u8;
                                    if v_isSharedCheck_1750_ == 0 {
                                        v___x_1743_ = v_a_1735_;
                                        v_isShared_1744_ = v_isSharedCheck_1750_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_fixed_1741_);
                                        lean_inc(v_visited_1740_);
                                        lean_dec(v_a_1735_);
                                        v___x_1743_ = lean_box(0);
                                        v_isShared_1744_ = v_isSharedCheck_1750_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v_a_1711_ = v___x_1718_;
                                    v_a_1712_ = v_a_1735_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_1734_);
                                v_a_1711_ = v___x_1718_;
                                v_a_1712_ = v_a_1735_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_1706_);
                            v_a_1751_ = lean_ctor_get(v___x_1733_, 0);
                            v_a_1752_ = lean_ctor_get(v___x_1733_, 1);
                            v_isSharedCheck_1759_ = (!lean_is_exclusive(v___x_1733_)) as u8;
                            if v_isSharedCheck_1759_ == 0 {
                                v___x_1754_ = v___x_1733_;
                                v_isShared_1755_ = v_isSharedCheck_1759_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1752_);
                                lean_inc(v_a_1751_);
                                lean_dec(v___x_1733_);
                                v___x_1754_ = lean_box(0);
                                v_isShared_1755_ = v_isSharedCheck_1759_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1713_ = lean_unsigned_to_nat(1);
                v___x_1714_ = lean_nat_add(v_a_1706_, v___x_1713_);
                lean_dec(v_a_1706_);
                v_a_1706_ = v___x_1714_;
                v_b_1707_ = v_a_1711_;
                v___y_1709_ = v_a_1712_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1726_ = lean_box((v___x_1720_) as usize);
                v___x_1727_ = lean_array_set(v_fixed_1722_, v_a_1706_, v___x_1726_);
                if v_isShared_1725_ == 0 {
                    lean_ctor_set(v___x_1724_, 1, v___x_1727_);
                    v___x_1729_ = v___x_1724_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_visited_1721_);
                    lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1727_);
                    v___x_1729_ = v_reuseFailAlloc_1730_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_1711_ = v___x_1718_;
                v_a_1712_ = v___x_1729_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1745_ = lean_box((v___x_1739_) as usize);
                v___x_1746_ = lean_array_set(v_fixed_1741_, v_a_1706_, v___x_1745_);
                if v_isShared_1744_ == 0 {
                    lean_ctor_set(v___x_1743_, 1, v___x_1746_);
                    v___x_1748_ = v___x_1743_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_visited_1740_);
                    lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1746_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_1711_ = v___x_1718_;
                v_a_1712_ = v___x_1748_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_1755_ == 0 {
                    v___x_1757_ = v___x_1754_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1751_);
                    lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_a_1752_);
                    v___x_1757_ = v_reuseFailAlloc_1758_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg___boxed(
    mut v_upperBound_1760_: *mut LeanObject,
    mut v_args_1761_: *mut LeanObject,
    mut v_a_1762_: *mut LeanObject,
    mut v_b_1763_: *mut LeanObject,
    mut v___y_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1766_: *mut LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_1760_, v_args_1761_, v_a_1762_, v_b_1763_, v___y_1764_, v___y_1765_);
    lean_dec_ref(v___y_1764_);
    lean_dec_ref(v_args_1761_);
    lean_dec(v_upperBound_1760_);
    return v_res_1766_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(
    mut v_xs_1767_: *mut LeanObject,
    mut v_ys_1768_: *mut LeanObject,
    mut v_x_1769_: *mut LeanObject,
) -> u8 {
    let mut v_zero_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1771_: u8 = 0;
    let mut v_one_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1770_ = lean_unsigned_to_nat(0);
                v_isZero_1771_ = lean_nat_dec_eq(v_x_1769_, v_zero_1770_);
                if v_isZero_1771_ == 1 {
                    lean_dec(v_x_1769_);
                    return v_isZero_1771_;
                } else {
                    v_one_1772_ = lean_unsigned_to_nat(1);
                    v_n_1773_ = lean_nat_sub(v_x_1769_, v_one_1772_);
                    lean_dec(v_x_1769_);
                    v___x_1774_ = lean_array_fget_borrowed(v_xs_1767_, v_n_1773_);
                    v___x_1775_ = lean_array_fget_borrowed(v_ys_1768_, v_n_1773_);
                    v___x_1776_ = l_Lean_Compiler_LCNF_FixedParams_instBEqAbsValue_beq(
                        v___x_1774_,
                        v___x_1775_,
                    );
                    if v___x_1776_ == 0 {
                        lean_dec(v_n_1773_);
                        return v___x_1776_;
                    } else {
                        v_x_1769_ = v_n_1773_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_xs_1778_: *mut LeanObject,
    mut v_ys_1779_: *mut LeanObject,
    mut v_x_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1781_: u8 = 0;
    let mut v_r_1782_: *mut LeanObject = core::ptr::null_mut();
    v_res_1781_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_1778_, v_ys_1779_, v_x_1780_);
    lean_dec_ref(v_ys_1779_);
    lean_dec_ref(v_xs_1778_);
    v_r_1782_ = lean_box((v_res_1781_) as usize);
    return v_r_1782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(
    mut v_a_1783_: *mut LeanObject,
    mut v_x_1784_: *mut LeanObject,
) -> u8 {
    let mut v___x_1785_: u8 = 0;
    let mut v_key_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1789_: u8 = 0;
    let mut v_fst_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: u8 = 0;
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: u8 = 0;
    let mut v___x_1800_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1784_) == 0 {
                    v___x_1785_ = 0;
                    return v___x_1785_;
                } else {
                    v_key_1786_ = lean_ctor_get(v_x_1784_, 0);
                    v_tail_1787_ = lean_ctor_get(v_x_1784_, 2);
                    v_fst_1791_ = lean_ctor_get(v_key_1786_, 0);
                    v_snd_1792_ = lean_ctor_get(v_key_1786_, 1);
                    v_fst_1793_ = lean_ctor_get(v_a_1783_, 0);
                    v_snd_1794_ = lean_ctor_get(v_a_1783_, 1);
                    v___x_1795_ = lean_name_eq(v_fst_1791_, v_fst_1793_);
                    if v___x_1795_ == 0 {
                        v___y_1789_ = v___x_1795_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1796_ = lean_array_get_size(v_snd_1792_);
                        v___x_1797_ = lean_array_get_size(v_snd_1794_);
                        v___x_1798_ = lean_nat_dec_eq(v___x_1796_, v___x_1797_);
                        if v___x_1798_ == 0 {
                            v_x_1784_ = v_tail_1787_;
                            state = 0;
                            continue;
                        } else {
                            v___x_1800_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_snd_1792_, v_snd_1794_, v___x_1796_);
                            v___y_1789_ = v___x_1800_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_1789_ == 0 {
                    v_x_1784_ = v_tail_1787_;
                    state = 0;
                    continue;
                } else {
                    return v___y_1789_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg___boxed(
    mut v_a_1801_: *mut LeanObject,
    mut v_x_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1803_: u8 = 0;
    let mut v_r_1804_: *mut LeanObject = core::ptr::null_mut();
    v_res_1803_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1801_, v_x_1802_);
    lean_dec(v_x_1802_);
    lean_dec_ref(v_a_1801_);
    v_r_1804_ = lean_box((v_res_1803_) as usize);
    return v_r_1804_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(
    mut v_as_1805_: *mut LeanObject,
    mut v_i_1806_: usize,
    mut v_stop_1807_: usize,
    mut v_b_1808_: u64,
) -> u64 {
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: u64 = 0;
    let mut v___x_1812_: u64 = 0;
    let mut v___x_1813_: usize = 0;
    let mut v___x_1814_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1809_ = lean_usize_dec_eq(v_i_1806_, v_stop_1807_);
                if v___x_1809_ == 0 {
                    v___x_1810_ = lean_array_uget_borrowed(v_as_1805_, v_i_1806_);
                    v___x_1811_ =
                        l_Lean_Compiler_LCNF_FixedParams_instHashableAbsValue_hash(v___x_1810_);
                    v___x_1812_ = lean_uint64_mix_hash(v_b_1808_, v___x_1811_);
                    v___x_1813_ = 1usize;
                    v___x_1814_ = lean_usize_add(v_i_1806_, v___x_1813_);
                    v_i_1806_ = v___x_1814_;
                    v_b_1808_ = v___x_1812_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1808_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2___boxed(
    mut v_as_1816_: *mut LeanObject,
    mut v_i_1817_: *mut LeanObject,
    mut v_stop_1818_: *mut LeanObject,
    mut v_b_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1820_: usize = 0;
    let mut v_stop_boxed_1821_: usize = 0;
    let mut v_b_boxed_1822_: u64 = 0;
    let mut v_res_1823_: u64 = 0;
    let mut v_r_1824_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1820_ = lean_unbox_usize(v_i_1817_);
    lean_dec(v_i_1817_);
    v_stop_boxed_1821_ = lean_unbox_usize(v_stop_1818_);
    lean_dec(v_stop_1818_);
    v_b_boxed_1822_ = lean_unbox_uint64(v_b_1819_);
    lean_dec_ref(v_b_1819_);
    v_res_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_as_1816_, v_i_boxed_1820_, v_stop_boxed_1821_, v_b_boxed_1822_);
    lean_dec_ref(v_as_1816_);
    v_r_1824_ = lean_box_uint64(v_res_1823_);
    return v_r_1824_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0()
-> u64 {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: u64 = 0;
    v___x_1825_ = lean_unsigned_to_nat(1723);
    v___x_1826_ = lean_uint64_of_nat(v___x_1825_);
    return v___x_1826_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(
    mut v_x_1827_: *mut LeanObject,
    mut v_x_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v_fst_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1839_: u64 = 0;
    let mut v___y_1840_: u64 = 0;
    let mut v___x_1841_: u64 = 0;
    let mut v___x_1842_: u64 = 0;
    let mut v___x_1843_: u64 = 0;
    let mut v_fold_1844_: u64 = 0;
    let mut v___x_1845_: u64 = 0;
    let mut v___x_1846_: u64 = 0;
    let mut v___x_1847_: u64 = 0;
    let mut v___x_1848_: usize = 0;
    let mut v___x_1849_: usize = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1860_: u64 = 0;
    let mut v___x_1861_: u64 = 0;
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: u8 = 0;
    let mut v___x_1866_: usize = 0;
    let mut v___x_1867_: usize = 0;
    let mut v___x_1868_: u64 = 0;
    let mut v___x_1869_: usize = 0;
    let mut v___x_1870_: usize = 0;
    let mut v___x_1871_: u64 = 0;
    let mut v___x_1872_: u64 = 0;
    let mut v_hash_1873_: u64 = 0;
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1828_) == 0 {
                    return v_x_1827_;
                } else {
                    v_key_1829_ = lean_ctor_get(v_x_1828_, 0);
                    v_value_1830_ = lean_ctor_get(v_x_1828_, 1);
                    v_tail_1831_ = lean_ctor_get(v_x_1828_, 2);
                    v_isSharedCheck_1874_ = (!lean_is_exclusive(v_x_1828_)) as u8;
                    if v_isSharedCheck_1874_ == 0 {
                        v___x_1833_ = v_x_1828_;
                        v_isShared_1834_ = v_isSharedCheck_1874_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1831_);
                        lean_inc(v_value_1830_);
                        lean_inc(v_key_1829_);
                        lean_dec(v_x_1828_);
                        v___x_1833_ = lean_box(0);
                        v_isShared_1834_ = v_isSharedCheck_1874_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1835_ = lean_ctor_get(v_key_1829_, 0);
                v_snd_1836_ = lean_ctor_get(v_key_1829_, 1);
                v___x_1837_ = lean_array_get_size(v_x_1827_);
                if lean_obj_tag(v_fst_1835_) == 0 {
                    v___x_1872_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0);
                    v___y_1860_ = v___x_1872_;
                    state = 4;
                    continue;
                } else {
                    v_hash_1873_ = lean_ctor_get_uint64(
                        v_fst_1835_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1860_ = v_hash_1873_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_1841_ = lean_uint64_mix_hash(v___y_1839_, v___y_1840_);
                v___x_1842_ = 32u64;
                v___x_1843_ = lean_uint64_shift_right(v___x_1841_, v___x_1842_);
                v_fold_1844_ = lean_uint64_xor(v___x_1841_, v___x_1843_);
                v___x_1845_ = 16u64;
                v___x_1846_ = lean_uint64_shift_right(v_fold_1844_, v___x_1845_);
                v___x_1847_ = lean_uint64_xor(v_fold_1844_, v___x_1846_);
                v___x_1848_ = lean_uint64_to_usize(v___x_1847_);
                v___x_1849_ = lean_usize_of_nat(v___x_1837_);
                v___x_1850_ = 1usize;
                v___x_1851_ = lean_usize_sub(v___x_1849_, v___x_1850_);
                v___x_1852_ = lean_usize_land(v___x_1848_, v___x_1851_);
                v___x_1853_ = lean_array_uget_borrowed(v_x_1827_, v___x_1852_);
                lean_inc(v___x_1853_);
                if v_isShared_1834_ == 0 {
                    lean_ctor_set(v___x_1833_, 2, v___x_1853_);
                    v___x_1855_ = v___x_1833_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_key_1829_);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_value_1830_);
                    lean_ctor_set(v_reuseFailAlloc_1858_, 2, v___x_1853_);
                    v___x_1855_ = v_reuseFailAlloc_1858_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1856_ = lean_array_uset(v_x_1827_, v___x_1852_, v___x_1855_);
                v_x_1827_ = v___x_1856_;
                v_x_1828_ = v_tail_1831_;
                state = 0;
                continue;
            }
            4 => {
                v___x_1861_ = 7u64;
                v___x_1862_ = lean_unsigned_to_nat(0);
                v___x_1863_ = lean_array_get_size(v_snd_1836_);
                v___x_1864_ = lean_nat_dec_lt(v___x_1862_, v___x_1863_);
                if v___x_1864_ == 0 {
                    v___y_1839_ = v___y_1860_;
                    v___y_1840_ = v___x_1861_;
                    state = 2;
                    continue;
                } else {
                    v___x_1865_ = lean_nat_dec_le(v___x_1863_, v___x_1863_);
                    if v___x_1865_ == 0 {
                        if v___x_1864_ == 0 {
                            v___y_1839_ = v___y_1860_;
                            v___y_1840_ = v___x_1861_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1866_ = 0usize;
                            v___x_1867_ = lean_usize_of_nat(v___x_1863_);
                            v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_1836_, v___x_1866_, v___x_1867_, v___x_1861_);
                            v___y_1839_ = v___y_1860_;
                            v___y_1840_ = v___x_1868_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1869_ = 0usize;
                        v___x_1870_ = lean_usize_of_nat(v___x_1863_);
                        v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_1836_, v___x_1869_, v___x_1870_, v___x_1861_);
                        v___y_1839_ = v___y_1860_;
                        v___y_1840_ = v___x_1871_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(
    mut v_i_1875_: *mut LeanObject,
    mut v_source_1876_: *mut LeanObject,
    mut v_target_1877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v_es_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1878_ = lean_array_get_size(v_source_1876_);
                v___x_1879_ = lean_nat_dec_lt(v_i_1875_, v___x_1878_);
                if v___x_1879_ == 0 {
                    lean_dec_ref(v_source_1876_);
                    lean_dec(v_i_1875_);
                    return v_target_1877_;
                } else {
                    v_es_1880_ = lean_array_fget(v_source_1876_, v_i_1875_);
                    v___x_1881_ = lean_box(0);
                    v_source_1882_ = lean_array_fset(v_source_1876_, v_i_1875_, v___x_1881_);
                    v_target_1883_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_target_1877_, v_es_1880_);
                    v___x_1884_ = lean_unsigned_to_nat(1);
                    v___x_1885_ = lean_nat_add(v_i_1875_, v___x_1884_);
                    lean_dec(v_i_1875_);
                    v_i_1875_ = v___x_1885_;
                    v_source_1876_ = v_source_1882_;
                    v_target_1877_ = v_target_1883_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(
    mut v_data_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1888_ = lean_array_get_size(v_data_1887_);
    v___x_1889_ = lean_unsigned_to_nat(2);
    v_nbuckets_1890_ = lean_nat_mul(v___x_1888_, v___x_1889_);
    v___x_1891_ = lean_unsigned_to_nat(0);
    v___x_1892_ = lean_box(0);
    v___x_1893_ = lean_mk_array(v_nbuckets_1890_, v___x_1892_);
    v___x_1894_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v___x_1891_, v_data_1887_, v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(
    mut v_m_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
    mut v_b_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1904_: u64 = 0;
    let mut v___y_1905_: u64 = 0;
    let mut v___x_1906_: u64 = 0;
    let mut v___x_1907_: u64 = 0;
    let mut v___x_1908_: u64 = 0;
    let mut v_fold_1909_: u64 = 0;
    let mut v___x_1910_: u64 = 0;
    let mut v___x_1911_: u64 = 0;
    let mut v___x_1912_: u64 = 0;
    let mut v___x_1913_: usize = 0;
    let mut v___x_1914_: usize = 0;
    let mut v___x_1915_: usize = 0;
    let mut v___x_1916_: usize = 0;
    let mut v___x_1917_: usize = 0;
    let mut v_bkt_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u8 = 0;
    let mut v_val_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v_unused_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1944_: u64 = 0;
    let mut v___x_1945_: u64 = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: usize = 0;
    let mut v___x_1951_: usize = 0;
    let mut v___x_1952_: u64 = 0;
    let mut v___x_1953_: usize = 0;
    let mut v___x_1954_: usize = 0;
    let mut v___x_1955_: u64 = 0;
    let mut v___x_1956_: u64 = 0;
    let mut v_hash_1957_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1898_ = lean_ctor_get(v_m_1895_, 0);
                v_buckets_1899_ = lean_ctor_get(v_m_1895_, 1);
                v_fst_1900_ = lean_ctor_get(v_a_1896_, 0);
                v_snd_1901_ = lean_ctor_get(v_a_1896_, 1);
                v___x_1902_ = lean_array_get_size(v_buckets_1899_);
                if lean_obj_tag(v_fst_1900_) == 0 {
                    v___x_1956_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0);
                    v___y_1944_ = v___x_1956_;
                    state = 5;
                    continue;
                } else {
                    v_hash_1957_ = lean_ctor_get_uint64(
                        v_fst_1900_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1944_ = v_hash_1957_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_1906_ = lean_uint64_mix_hash(v___y_1904_, v___y_1905_);
                v___x_1907_ = 32u64;
                v___x_1908_ = lean_uint64_shift_right(v___x_1906_, v___x_1907_);
                v_fold_1909_ = lean_uint64_xor(v___x_1906_, v___x_1908_);
                v___x_1910_ = 16u64;
                v___x_1911_ = lean_uint64_shift_right(v_fold_1909_, v___x_1910_);
                v___x_1912_ = lean_uint64_xor(v_fold_1909_, v___x_1911_);
                v___x_1913_ = lean_uint64_to_usize(v___x_1912_);
                v___x_1914_ = lean_usize_of_nat(v___x_1902_);
                v___x_1915_ = 1usize;
                v___x_1916_ = lean_usize_sub(v___x_1914_, v___x_1915_);
                v___x_1917_ = lean_usize_land(v___x_1913_, v___x_1916_);
                v_bkt_1918_ = lean_array_uget_borrowed(v_buckets_1899_, v___x_1917_);
                v___x_1919_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1896_, v_bkt_1918_);
                if v___x_1919_ == 0 {
                    lean_inc_ref(v_buckets_1899_);
                    lean_inc(v_size_1898_);
                    v_isSharedCheck_1940_ = (!lean_is_exclusive(v_m_1895_)) as u8;
                    if v_isSharedCheck_1940_ == 0 {
                        v_unused_1941_ = lean_ctor_get(v_m_1895_, 1);
                        lean_dec(v_unused_1941_);
                        v_unused_1942_ = lean_ctor_get(v_m_1895_, 0);
                        lean_dec(v_unused_1942_);
                        v___x_1921_ = v_m_1895_;
                        v_isShared_1922_ = v_isSharedCheck_1940_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_1895_);
                        v___x_1921_ = lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1940_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_1897_);
                    lean_dec_ref(v_a_1896_);
                    return v_m_1895_;
                }
            }
            2 => {
                v___x_1923_ = lean_unsigned_to_nat(1);
                v_size_x27_1924_ = lean_nat_add(v_size_1898_, v___x_1923_);
                lean_dec(v_size_1898_);
                lean_inc(v_bkt_1918_);
                v___x_1925_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1925_, 0, v_a_1896_);
                lean_ctor_set(v___x_1925_, 1, v_b_1897_);
                lean_ctor_set(v___x_1925_, 2, v_bkt_1918_);
                v_buckets_x27_1926_ = lean_array_uset(v_buckets_1899_, v___x_1917_, v___x_1925_);
                v___x_1927_ = lean_unsigned_to_nat(4);
                v___x_1928_ = lean_nat_mul(v_size_x27_1924_, v___x_1927_);
                v___x_1929_ = lean_unsigned_to_nat(3);
                v___x_1930_ = lean_nat_div(v___x_1928_, v___x_1929_);
                lean_dec(v___x_1928_);
                v___x_1931_ = lean_array_get_size(v_buckets_x27_1926_);
                v___x_1932_ = lean_nat_dec_le(v___x_1930_, v___x_1931_);
                lean_dec(v___x_1930_);
                if v___x_1932_ == 0 {
                    v_val_1933_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_buckets_x27_1926_);
                    if v_isShared_1922_ == 0 {
                        lean_ctor_set(v___x_1921_, 1, v_val_1933_);
                        lean_ctor_set(v___x_1921_, 0, v_size_x27_1924_);
                        v___x_1935_ = v___x_1921_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_size_x27_1924_);
                        lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_val_1933_);
                        v___x_1935_ = v_reuseFailAlloc_1936_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1922_ == 0 {
                        lean_ctor_set(v___x_1921_, 1, v_buckets_x27_1926_);
                        lean_ctor_set(v___x_1921_, 0, v_size_x27_1924_);
                        v___x_1938_ = v___x_1921_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_size_x27_1924_);
                        lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_buckets_x27_1926_);
                        v___x_1938_ = v_reuseFailAlloc_1939_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1935_;
            }
            4 => {
                return v___x_1938_;
            }
            5 => {
                v___x_1945_ = 7u64;
                v___x_1946_ = lean_unsigned_to_nat(0);
                v___x_1947_ = lean_array_get_size(v_snd_1901_);
                v___x_1948_ = lean_nat_dec_lt(v___x_1946_, v___x_1947_);
                if v___x_1948_ == 0 {
                    v___y_1904_ = v___y_1944_;
                    v___y_1905_ = v___x_1945_;
                    state = 1;
                    continue;
                } else {
                    v___x_1949_ = lean_nat_dec_le(v___x_1947_, v___x_1947_);
                    if v___x_1949_ == 0 {
                        if v___x_1948_ == 0 {
                            v___y_1904_ = v___y_1944_;
                            v___y_1905_ = v___x_1945_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1950_ = 0usize;
                            v___x_1951_ = lean_usize_of_nat(v___x_1947_);
                            v___x_1952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_1901_, v___x_1950_, v___x_1951_, v___x_1945_);
                            v___y_1904_ = v___y_1944_;
                            v___y_1905_ = v___x_1952_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1953_ = 0usize;
                        v___x_1954_ = lean_usize_of_nat(v___x_1947_);
                        v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_1901_, v___x_1953_, v___x_1954_, v___x_1945_);
                        v___y_1904_ = v___y_1944_;
                        v___y_1905_ = v___x_1955_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(
    mut v_f_1958_: *mut LeanObject,
    mut v_v_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_v_1959_) == 0 {
        let mut v_code_1962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
        v_code_1962_ = lean_ctor_get(v_v_1959_, 0);
        lean_inc_ref(v_code_1962_);
        lean_dec_ref_known(v_v_1959_, 1);
        lean_inc_ref(v___y_1960_);
        v___x_1963_ = lean_apply_3(v_f_1958_, v_code_1962_, v___y_1960_, v___y_1961_);
        return v___x_1963_;
    } else {
        let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_v_1959_, 1);
        lean_dec_ref(v_f_1958_);
        v___x_1964_ = lean_box(0);
        v___x_1965_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1965_, 0, v___x_1964_);
        lean_ctor_set(v___x_1965_, 1, v___y_1961_);
        return v___x_1965_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg___boxed(
    mut v_f_1966_: *mut LeanObject,
    mut v_v_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1970_: *mut LeanObject = core::ptr::null_mut();
    v_res_1970_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_1966_, v_v_1967_, v___y_1968_, v___y_1969_);
    lean_dec_ref(v___y_1968_);
    return v_res_1970_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(
    mut v_m_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1978_: u64 = 0;
    let mut v___y_1979_: u64 = 0;
    let mut v___x_1980_: u64 = 0;
    let mut v___x_1981_: u64 = 0;
    let mut v___x_1982_: u64 = 0;
    let mut v_fold_1983_: u64 = 0;
    let mut v___x_1984_: u64 = 0;
    let mut v___x_1985_: u64 = 0;
    let mut v___x_1986_: u64 = 0;
    let mut v___x_1987_: usize = 0;
    let mut v___x_1988_: usize = 0;
    let mut v___x_1989_: usize = 0;
    let mut v___x_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v___y_1995_: u64 = 0;
    let mut v___x_1996_: u64 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: usize = 0;
    let mut v___x_2002_: usize = 0;
    let mut v___x_2003_: u64 = 0;
    let mut v___x_2004_: usize = 0;
    let mut v___x_2005_: usize = 0;
    let mut v___x_2006_: u64 = 0;
    let mut v___x_2007_: u64 = 0;
    let mut v_hash_2008_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1973_ = lean_ctor_get(v_m_1971_, 1);
                v_fst_1974_ = lean_ctor_get(v_a_1972_, 0);
                v_snd_1975_ = lean_ctor_get(v_a_1972_, 1);
                v___x_1976_ = lean_array_get_size(v_buckets_1973_);
                if lean_obj_tag(v_fst_1974_) == 0 {
                    v___x_2007_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg___closed__0);
                    v___y_1995_ = v___x_2007_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2008_ = lean_ctor_get_uint64(
                        v_fst_1974_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1995_ = v_hash_2008_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1980_ = lean_uint64_mix_hash(v___y_1978_, v___y_1979_);
                v___x_1981_ = 32u64;
                v___x_1982_ = lean_uint64_shift_right(v___x_1980_, v___x_1981_);
                v_fold_1983_ = lean_uint64_xor(v___x_1980_, v___x_1982_);
                v___x_1984_ = 16u64;
                v___x_1985_ = lean_uint64_shift_right(v_fold_1983_, v___x_1984_);
                v___x_1986_ = lean_uint64_xor(v_fold_1983_, v___x_1985_);
                v___x_1987_ = lean_uint64_to_usize(v___x_1986_);
                v___x_1988_ = lean_usize_of_nat(v___x_1976_);
                v___x_1989_ = 1usize;
                v___x_1990_ = lean_usize_sub(v___x_1988_, v___x_1989_);
                v___x_1991_ = lean_usize_land(v___x_1987_, v___x_1990_);
                v___x_1992_ = lean_array_uget_borrowed(v_buckets_1973_, v___x_1991_);
                v___x_1993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_1972_, v___x_1992_);
                return v___x_1993_;
            }
            2 => {
                v___x_1996_ = 7u64;
                v___x_1997_ = lean_unsigned_to_nat(0);
                v___x_1998_ = lean_array_get_size(v_snd_1975_);
                v___x_1999_ = lean_nat_dec_lt(v___x_1997_, v___x_1998_);
                if v___x_1999_ == 0 {
                    v___y_1978_ = v___y_1995_;
                    v___y_1979_ = v___x_1996_;
                    state = 1;
                    continue;
                } else {
                    v___x_2000_ = lean_nat_dec_le(v___x_1998_, v___x_1998_);
                    if v___x_2000_ == 0 {
                        if v___x_1999_ == 0 {
                            v___y_1978_ = v___y_1995_;
                            v___y_1979_ = v___x_1996_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2001_ = 0usize;
                            v___x_2002_ = lean_usize_of_nat(v___x_1998_);
                            v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_1975_, v___x_2001_, v___x_2002_, v___x_1996_);
                            v___y_1978_ = v___y_1995_;
                            v___y_1979_ = v___x_2003_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2004_ = 0usize;
                        v___x_2005_ = lean_usize_of_nat(v___x_1998_);
                        v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__2(v_snd_1975_, v___x_2004_, v___x_2005_, v___x_1996_);
                        v___y_1978_ = v___y_1995_;
                        v___y_1979_ = v___x_2006_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg___boxed(
    mut v_m_2009_: *mut LeanObject,
    mut v_a_2010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2011_: u8 = 0;
    let mut v_r_2012_: *mut LeanObject = core::ptr::null_mut();
    v_res_2011_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_2009_, v_a_2010_);
    lean_dec_ref(v_a_2010_);
    lean_dec_ref(v_m_2009_);
    v_r_2012_ = lean_box((v_res_2011_) as usize);
    return v_r_2012_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(
    mut v_upperBound_2013_: *mut LeanObject,
    mut v_args_2014_: *mut LeanObject,
    mut v_a_2015_: *mut LeanObject,
    mut v_b_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
    mut v___y_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: u8 = 0;
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2025_ = lean_nat_dec_lt(v_a_2015_, v_upperBound_2013_);
                if v___x_2025_ == 0 {
                    lean_dec(v_a_2015_);
                    v___x_2026_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2026_, 0, v_b_2016_);
                    lean_ctor_set(v___x_2026_, 1, v___y_2018_);
                    return v___x_2026_;
                } else {
                    v___x_2027_ = lean_array_get_size(v_args_2014_);
                    v___x_2028_ = lean_nat_dec_lt(v_a_2015_, v___x_2027_);
                    if v___x_2028_ == 0 {
                        v___x_2029_ = lean_box(0);
                        v___x_2030_ = lean_array_push(v_b_2016_, v___x_2029_);
                        v_a_2020_ = v___x_2030_;
                        v_a_2021_ = v___y_2018_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2031_ = lean_array_fget_borrowed(v_args_2014_, v_a_2015_);
                        v___x_2032_ = l_Lean_Compiler_LCNF_FixedParams_evalArg(
                            v___x_2031_,
                            v___y_2017_,
                            v___y_2018_,
                        );
                        if lean_obj_tag(v___x_2032_) == 0 {
                            v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
                            lean_inc(v_a_2033_);
                            v_a_2034_ = lean_ctor_get(v___x_2032_, 1);
                            lean_inc(v_a_2034_);
                            lean_dec_ref_known(v___x_2032_, 2);
                            v___x_2035_ = lean_array_push(v_b_2016_, v_a_2033_);
                            v_a_2020_ = v___x_2035_;
                            v_a_2021_ = v_a_2034_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_2016_);
                            lean_dec(v_a_2015_);
                            v_a_2036_ = lean_ctor_get(v___x_2032_, 0);
                            v_a_2037_ = lean_ctor_get(v___x_2032_, 1);
                            v_isSharedCheck_2044_ = (!lean_is_exclusive(v___x_2032_)) as u8;
                            if v_isSharedCheck_2044_ == 0 {
                                v___x_2039_ = v___x_2032_;
                                v_isShared_2040_ = v_isSharedCheck_2044_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2037_);
                                lean_inc(v_a_2036_);
                                lean_dec(v___x_2032_);
                                v___x_2039_ = lean_box(0);
                                v_isShared_2040_ = v_isSharedCheck_2044_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2022_ = lean_unsigned_to_nat(1);
                v___x_2023_ = lean_nat_add(v_a_2015_, v___x_2022_);
                lean_dec(v_a_2015_);
                v_a_2015_ = v___x_2023_;
                v_b_2016_ = v_a_2020_;
                v___y_2018_ = v_a_2021_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2040_ == 0 {
                    v___x_2042_ = v___x_2039_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2036_);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_a_2037_);
                    v___x_2042_ = v_reuseFailAlloc_2043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg___boxed(
    mut v_upperBound_2045_: *mut LeanObject,
    mut v_args_2046_: *mut LeanObject,
    mut v_a_2047_: *mut LeanObject,
    mut v_b_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
    mut v___y_2050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2051_: *mut LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_2045_, v_args_2046_, v_a_2047_, v_b_2048_, v___y_2049_, v___y_2050_);
    lean_dec_ref(v___y_2049_);
    lean_dec_ref(v_args_2046_);
    lean_dec(v_upperBound_2045_);
    return v_res_2051_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(
    mut v_a_2052_: u8,
    mut v_as_2053_: *mut LeanObject,
    mut v_i_2054_: usize,
    mut v_stop_2055_: usize,
) -> u8 {
    let mut v___x_2057_: usize = 0;
    let mut v___x_2058_: usize = 0;
    let mut v___x_2060_: u8 = 0;
    let mut v___x_2061_: u8 = 0;
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: u8 = 0;
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2060_ = lean_usize_dec_eq(v_i_2054_, v_stop_2055_);
                if v___x_2060_ == 0 {
                    v___x_2061_ = 1;
                    v___x_2062_ = lean_array_uget_borrowed(v_as_2053_, v_i_2054_);
                    if v_a_2052_ == 0 {
                        v___x_2063_ = (lean_unbox(v___x_2062_) as u8);
                        if v___x_2063_ == 0 {
                            return v___x_2061_;
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2064_ = (lean_unbox(v___x_2062_) as u8);
                        if v___x_2064_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_2061_;
                        }
                    }
                } else {
                    v___x_2065_ = 0;
                    return v___x_2065_;
                }
            }
            1 => {
                v___x_2057_ = 1usize;
                v___x_2058_ = lean_usize_add(v_i_2054_, v___x_2057_);
                v_i_2054_ = v___x_2058_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9___boxed(
    mut v_a_2066_: *mut LeanObject,
    mut v_as_2067_: *mut LeanObject,
    mut v_i_2068_: *mut LeanObject,
    mut v_stop_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2070_: u8 = 0;
    let mut v_i_boxed_2071_: usize = 0;
    let mut v_stop_boxed_2072_: usize = 0;
    let mut v_res_2073_: u8 = 0;
    let mut v_r_2074_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2070_ = (lean_unbox(v_a_2066_) as u8);
    v_i_boxed_2071_ = lean_unbox_usize(v_i_2068_);
    lean_dec(v_i_2068_);
    v_stop_boxed_2072_ = lean_unbox_usize(v_stop_2069_);
    lean_dec(v_stop_2069_);
    v_res_2073_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_boxed_2070_, v_as_2067_, v_i_boxed_2071_, v_stop_boxed_2072_);
    lean_dec_ref(v_as_2067_);
    v_r_2074_ = lean_box((v_res_2073_) as usize);
    return v_r_2074_;
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(
    mut v_as_2075_: *mut LeanObject,
    mut v_a_2076_: u8,
) -> u8 {
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: u8 = 0;
    v___x_2077_ = lean_unsigned_to_nat(0);
    v___x_2078_ = lean_array_get_size(v_as_2075_);
    v___x_2079_ = lean_nat_dec_lt(v___x_2077_, v___x_2078_);
    if v___x_2079_ == 0 {
        return v___x_2079_;
    } else {
        if v___x_2079_ == 0 {
            return v___x_2079_;
        } else {
            let mut v___x_2080_: usize = 0;
            let mut v___x_2081_: usize = 0;
            let mut v___x_2082_: u8 = 0;
            v___x_2080_ = 0usize;
            v___x_2081_ = lean_usize_of_nat(v___x_2078_);
            v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6_spec__9(v_a_2076_, v_as_2075_, v___x_2080_, v___x_2081_);
            return v___x_2082_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6___boxed(
    mut v_as_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2085_: u8 = 0;
    let mut v_res_2086_: u8 = 0;
    let mut v_r_2087_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2085_ = (lean_unbox(v_a_2084_) as u8);
    v_res_2086_ = l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(
        v_as_2083_,
        v_a_boxed_2085_,
    );
    lean_dec_ref(v_as_2083_);
    v_r_2087_ = lean_box((v_res_2086_) as usize);
    return v_r_2087_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed(
    mut v_a_2090_: *mut LeanObject,
    mut v_a_2091_: *mut LeanObject,
    mut v_c_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2095_: *mut LeanObject = core::ptr::null_mut();
    v_res_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(v_a_2090_, v_a_2091_, v_c_2092_, v___y_2093_, v___y_2094_);
    lean_dec_ref(v___y_2093_);
    lean_dec_ref(v_a_2090_);
    return v_res_2095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(
    mut v_declName_2096_: *mut LeanObject,
    mut v_args_2097_: *mut LeanObject,
    mut v_as_2098_: *mut LeanObject,
    mut v_sz_2099_: usize,
    mut v_i_2100_: usize,
    mut v_b_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: usize = 0;
    let mut v___x_2108_: usize = 0;
    let mut v___x_2110_: u8 = 0;
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixed_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___f_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2139_: u8 = 0;
    let mut v_unused_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2110_ = lean_usize_dec_lt(v_i_2100_, v_sz_2099_);
                if v___x_2110_ == 0 {
                    lean_dec(v_declName_2096_);
                    v___x_2111_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2111_, 0, v_b_2101_);
                    lean_ctor_set(v___x_2111_, 1, v___y_2103_);
                    return v___x_2111_;
                } else {
                    v_a_2112_ = lean_array_uget_borrowed(v_as_2098_, v_i_2100_);
                    v_toSignature_2113_ = lean_ctor_get(v_a_2112_, 0);
                    v_value_2114_ = lean_ctor_get(v_a_2112_, 1);
                    v_name_2115_ = lean_ctor_get(v_toSignature_2113_, 0);
                    v_params_2116_ = lean_ctor_get(v_toSignature_2113_, 3);
                    v___x_2117_ = lean_box(0);
                    v___x_2118_ = lean_name_eq(v_declName_2096_, v_name_2115_);
                    if v___x_2118_ == 0 {
                        v_a_2105_ = v___x_2117_;
                        v_a_2106_ = v___y_2103_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2119_ = lean_array_get_size(v_params_2116_);
                        v___x_2120_ = lean_unsigned_to_nat(0);
                        v___x_2121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0;
                        v___x_2122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v___x_2119_, v_args_2097_, v___x_2120_, v___x_2121_, v___y_2102_, v___y_2103_);
                        if lean_obj_tag(v___x_2122_) == 0 {
                            v_a_2123_ = lean_ctor_get(v___x_2122_, 1);
                            lean_inc(v_a_2123_);
                            v_a_2124_ = lean_ctor_get(v___x_2122_, 0);
                            lean_inc_n(v_a_2124_, 2);
                            lean_dec_ref_known(v___x_2122_, 2);
                            v_visited_2125_ = lean_ctor_get(v_a_2123_, 0);
                            v_fixed_2126_ = lean_ctor_get(v_a_2123_, 1);
                            lean_inc(v_declName_2096_);
                            v___x_2127_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2127_, 0, v_declName_2096_);
                            lean_ctor_set(v___x_2127_, 1, v_a_2124_);
                            v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_visited_2125_, v___x_2127_);
                            if v___x_2128_ == 0 {
                                lean_inc_ref(v_fixed_2126_);
                                lean_inc_ref(v_visited_2125_);
                                v_isSharedCheck_2139_ = (!lean_is_exclusive(v_a_2123_)) as u8;
                                if v_isSharedCheck_2139_ == 0 {
                                    v_unused_2140_ = lean_ctor_get(v_a_2123_, 1);
                                    lean_dec(v_unused_2140_);
                                    v_unused_2141_ = lean_ctor_get(v_a_2123_, 0);
                                    lean_dec(v_unused_2141_);
                                    v___x_2130_ = v_a_2123_;
                                    v_isShared_2131_ = v_isSharedCheck_2139_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v_a_2123_);
                                    v___x_2130_ = lean_box(0);
                                    v_isShared_2131_ = v_isSharedCheck_2139_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v___x_2127_, 2);
                                lean_dec(v_a_2124_);
                                v_a_2105_ = v___x_2117_;
                                v_a_2106_ = v_a_2123_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_declName_2096_);
                            v_a_2142_ = lean_ctor_get(v___x_2122_, 0);
                            v_a_2143_ = lean_ctor_get(v___x_2122_, 1);
                            v_isSharedCheck_2150_ = (!lean_is_exclusive(v___x_2122_)) as u8;
                            if v_isSharedCheck_2150_ == 0 {
                                v___x_2145_ = v___x_2122_;
                                v_isShared_2146_ = v_isSharedCheck_2150_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2143_);
                                lean_inc(v_a_2142_);
                                lean_dec(v___x_2122_);
                                v___x_2145_ = lean_box(0);
                                v_isShared_2146_ = v_isSharedCheck_2150_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2107_ = 1usize;
                v___x_2108_ = lean_usize_add(v_i_2100_, v___x_2107_);
                v_i_2100_ = v___x_2108_;
                v_b_2101_ = v_a_2105_;
                v___y_2103_ = v_a_2106_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v_a_2112_);
                v___f_2132_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0___boxed as *mut core::ffi::c_void, 5, 2);
                lean_closure_set(v___f_2132_, 0, v_a_2112_);
                lean_closure_set(v___f_2132_, 1, v_a_2124_);
                v___x_2133_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_visited_2125_, v___x_2127_, v___x_2117_);
                if v_isShared_2131_ == 0 {
                    lean_ctor_set(v___x_2130_, 0, v___x_2133_);
                    v___x_2135_ = v___x_2130_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2133_);
                    lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_fixed_2126_);
                    v___x_2135_ = v_reuseFailAlloc_2138_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_value_2114_);
                v___x_2136_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v___f_2132_, v_value_2114_, v___y_2102_, v___x_2135_);
                if lean_obj_tag(v___x_2136_) == 0 {
                    v_a_2137_ = lean_ctor_get(v___x_2136_, 1);
                    lean_inc(v_a_2137_);
                    lean_dec_ref_known(v___x_2136_, 2);
                    v_a_2105_ = v___x_2117_;
                    v_a_2106_ = v_a_2137_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_declName_2096_);
                    return v___x_2136_;
                }
            }
            4 => {
                if v_isShared_2146_ == 0 {
                    v___x_2148_ = v___x_2145_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2142_);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_a_2143_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalApp(
    mut v_declName_2151_: *mut LeanObject,
    mut v_args_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2160_: usize = 0;
    let mut v___x_2161_: usize = 0;
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2166_: u8 = 0;
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2170_: u8 = 0;
    let mut v_unused_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_main_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2185_: u8 = 0;
    let mut v_fixed_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: u8 = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_unused_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_main_2172_ = lean_ctor_get(v_a_2153_, 1);
                v_toSignature_2173_ = lean_ctor_get(v_main_2172_, 0);
                v_decls_2174_ = lean_ctor_get(v_a_2153_, 0);
                v_name_2175_ = lean_ctor_get(v_toSignature_2173_, 0);
                v_params_2176_ = lean_ctor_get(v_toSignature_2173_, 3);
                v___x_2177_ = lean_name_eq(v_declName_2151_, v_name_2175_);
                if v___x_2177_ == 0 {
                    v___y_2156_ = v_a_2153_;
                    v_decls_2157_ = v_decls_2174_;
                    v___y_2158_ = v_a_2154_;
                    state = 1;
                    continue;
                } else {
                    v___x_2178_ = lean_array_get_size(v_params_2176_);
                    v___x_2179_ = lean_unsigned_to_nat(0);
                    v___x_2180_ = lean_box(0);
                    v___x_2181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v___x_2178_, v_args_2152_, v___x_2179_, v___x_2180_, v_a_2153_, v_a_2154_);
                    if lean_obj_tag(v___x_2181_) == 0 {
                        v_a_2182_ = lean_ctor_get(v___x_2181_, 1);
                        v_isSharedCheck_2191_ = (!lean_is_exclusive(v___x_2181_)) as u8;
                        if v_isSharedCheck_2191_ == 0 {
                            v_unused_2192_ = lean_ctor_get(v___x_2181_, 0);
                            lean_dec(v_unused_2192_);
                            v___x_2184_ = v___x_2181_;
                            v_isShared_2185_ = v_isSharedCheck_2191_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2182_);
                            lean_dec(v___x_2181_);
                            v___x_2184_ = lean_box(0);
                            v_isShared_2185_ = v_isSharedCheck_2191_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_2151_);
                        return v___x_2181_;
                    }
                }
            }
            1 => {
                v___x_2159_ = lean_box(0);
                v_sz_2160_ = lean_array_size(v_decls_2157_);
                v___x_2161_ = 0usize;
                v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_2151_, v_args_2152_, v_decls_2157_, v_sz_2160_, v___x_2161_, v___x_2159_, v___y_2156_, v___y_2158_);
                if lean_obj_tag(v___x_2162_) == 0 {
                    v_a_2163_ = lean_ctor_get(v___x_2162_, 1);
                    v_isSharedCheck_2170_ = (!lean_is_exclusive(v___x_2162_)) as u8;
                    if v_isSharedCheck_2170_ == 0 {
                        v_unused_2171_ = lean_ctor_get(v___x_2162_, 0);
                        lean_dec(v_unused_2171_);
                        v___x_2165_ = v___x_2162_;
                        v_isShared_2166_ = v_isSharedCheck_2170_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2163_);
                        lean_dec(v___x_2162_);
                        v___x_2165_ = lean_box(0);
                        v_isShared_2166_ = v_isSharedCheck_2170_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2162_;
                }
            }
            2 => {
                if v_isShared_2166_ == 0 {
                    lean_ctor_set(v___x_2165_, 0, v___x_2159_);
                    v___x_2168_ = v___x_2165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2159_);
                    lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_a_2163_);
                    v___x_2168_ = v_reuseFailAlloc_2169_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2168_;
            }
            4 => {
                v_fixed_2186_ = lean_ctor_get(v_a_2182_, 1);
                v___x_2187_ =
                    l_Array_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__6(
                        v_fixed_2186_,
                        v___x_2177_,
                    );
                if v___x_2187_ == 0 {
                    lean_dec(v_declName_2151_);
                    if v_isShared_2185_ == 0 {
                        lean_ctor_set_tag(v___x_2184_, 1);
                        lean_ctor_set(v___x_2184_, 0, v___x_2180_);
                        v___x_2189_ = v___x_2184_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2180_);
                        lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_a_2182_);
                        v___x_2189_ = v_reuseFailAlloc_2190_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2184_);
                    v___y_2156_ = v_a_2153_;
                    v_decls_2157_ = v_decls_2174_;
                    v___y_2158_ = v_a_2182_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                return v___x_2189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalLetValue(
    mut v_e_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_2193_) == 3 {
        let mut v_declName_2196_: *mut LeanObject = core::ptr::null_mut();
        let mut v_args_2197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
        v_declName_2196_ = lean_ctor_get(v_e_2193_, 0);
        lean_inc(v_declName_2196_);
        v_args_2197_ = lean_ctor_get(v_e_2193_, 2);
        lean_inc_ref(v_args_2197_);
        lean_dec_ref_known(v_e_2193_, 3);
        v___x_2198_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(
            v_declName_2196_,
            v_args_2197_,
            v_a_2194_,
            v_a_2195_,
        );
        lean_dec_ref(v_args_2197_);
        return v___x_2198_;
    } else {
        let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_e_2193_);
        v___x_2199_ = lean_box(0);
        v___x_2200_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2200_, 0, v___x_2199_);
        lean_ctor_set(v___x_2200_, 1, v_a_2195_);
        return v___x_2200_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(
    mut v_as_2201_: *mut LeanObject,
    mut v_i_2202_: usize,
    mut v_stop_2203_: usize,
    mut v_b_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: usize = 0;
    let mut v___x_2213_: usize = 0;
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2215_ = lean_usize_dec_eq(v_i_2202_, v_stop_2203_);
                if v___x_2215_ == 0 {
                    v___x_2216_ = lean_array_uget_borrowed(v_as_2201_, v_i_2202_);
                    match lean_obj_tag(v___x_2216_) {
                        0 => {
                            v_code_2217_ = lean_ctor_get(v___x_2216_, 2);
                            lean_inc_ref(v_code_2217_);
                            v___y_2208_ = v_code_2217_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_2218_ = lean_ctor_get(v___x_2216_, 1);
                            lean_inc_ref(v_code_2218_);
                            v___y_2208_ = v_code_2218_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_2219_ = lean_ctor_get(v___x_2216_, 0);
                            lean_inc_ref(v_code_2219_);
                            v___y_2208_ = v_code_2219_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2220_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2220_, 0, v_b_2204_);
                    lean_ctor_set(v___x_2220_, 1, v___y_2206_);
                    return v___x_2220_;
                }
            }
            1 => {
                lean_inc_ref(v___y_2205_);
                v___x_2209_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(
                    v___y_2208_,
                    v___y_2205_,
                    v___y_2206_,
                );
                if lean_obj_tag(v___x_2209_) == 0 {
                    v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
                    lean_inc(v_a_2210_);
                    v_a_2211_ = lean_ctor_get(v___x_2209_, 1);
                    lean_inc(v_a_2211_);
                    lean_dec_ref_known(v___x_2209_, 2);
                    v___x_2212_ = 1usize;
                    v___x_2213_ = lean_usize_add(v_i_2202_, v___x_2212_);
                    v_i_2202_ = v___x_2213_;
                    v_b_2204_ = v_a_2210_;
                    v___y_2206_ = v_a_2211_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2209_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalCode(
    mut v_code_2221_: *mut LeanObject,
    mut v_a_2222_: *mut LeanObject,
    mut v_a_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v_fvarId_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_main_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_a_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2259_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v_decl_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut v_unused_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: usize = 0;
    let mut v___x_2290_: usize = 0;
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_2221_) {
                0 => {
                    v_decl_2224_ = lean_ctor_get(v_code_2221_, 0);
                    lean_inc_ref(v_decl_2224_);
                    v_k_2225_ = lean_ctor_get(v_code_2221_, 1);
                    lean_inc_ref(v_k_2225_);
                    lean_dec_ref_known(v_code_2221_, 2);
                    v_value_2226_ = lean_ctor_get(v_decl_2224_, 3);
                    lean_inc(v_value_2226_);
                    lean_dec_ref(v_decl_2224_);
                    v___x_2227_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(
                        v_value_2226_,
                        v_a_2222_,
                        v_a_2223_,
                    );
                    if lean_obj_tag(v___x_2227_) == 0 {
                        v_a_2228_ = lean_ctor_get(v___x_2227_, 1);
                        lean_inc(v_a_2228_);
                        lean_dec_ref_known(v___x_2227_, 2);
                        v_code_2221_ = v_k_2225_;
                        v_a_2223_ = v_a_2228_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_2225_);
                        lean_dec_ref(v_a_2222_);
                        return v___x_2227_;
                    }
                }
                1 => {
                    v_decl_2230_ = lean_ctor_get(v_code_2221_, 0);
                    lean_inc_ref_n(v_decl_2230_, 2);
                    v_k_2231_ = lean_ctor_get(v_code_2221_, 1);
                    lean_inc_ref(v_k_2231_);
                    lean_dec_ref_known(v_code_2221_, 2);
                    v___x_2232_ = l_Lean_Compiler_LCNF_FixedParams_isEquivalentFunDecl_x3f(
                        v_decl_2230_,
                        v_a_2222_,
                        v_a_2223_,
                    );
                    if lean_obj_tag(v___x_2232_) == 0 {
                        v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
                        lean_inc(v_a_2233_);
                        if lean_obj_tag(v_a_2233_) == 1 {
                            v_a_2234_ = lean_ctor_get(v___x_2232_, 1);
                            lean_inc(v_a_2234_);
                            lean_dec_ref_known(v___x_2232_, 2);
                            v_val_2235_ = lean_ctor_get(v_a_2233_, 0);
                            v_isSharedCheck_2249_ = (!lean_is_exclusive(v_a_2233_)) as u8;
                            if v_isSharedCheck_2249_ == 0 {
                                v___x_2237_ = v_a_2233_;
                                v_isShared_2238_ = v_isSharedCheck_2249_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_val_2235_);
                                lean_dec(v_a_2233_);
                                v___x_2237_ = lean_box(0);
                                v_isShared_2238_ = v_isSharedCheck_2249_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2233_);
                            v_a_2250_ = lean_ctor_get(v___x_2232_, 1);
                            lean_inc(v_a_2250_);
                            lean_dec_ref_known(v___x_2232_, 2);
                            v_value_2251_ = lean_ctor_get(v_decl_2230_, 4);
                            lean_inc_ref(v_value_2251_);
                            lean_dec_ref(v_decl_2230_);
                            lean_inc_ref(v_a_2222_);
                            v___x_2252_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(
                                v_value_2251_,
                                v_a_2222_,
                                v_a_2250_,
                            );
                            if lean_obj_tag(v___x_2252_) == 0 {
                                v_a_2253_ = lean_ctor_get(v___x_2252_, 1);
                                lean_inc(v_a_2253_);
                                lean_dec_ref_known(v___x_2252_, 2);
                                v_code_2221_ = v_k_2231_;
                                v_a_2223_ = v_a_2253_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec_ref(v_k_2231_);
                                lean_dec_ref(v_a_2222_);
                                return v___x_2252_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_2231_);
                        lean_dec_ref(v_decl_2230_);
                        lean_dec_ref(v_a_2222_);
                        v_a_2255_ = lean_ctor_get(v___x_2232_, 0);
                        v_a_2256_ = lean_ctor_get(v___x_2232_, 1);
                        v_isSharedCheck_2263_ = (!lean_is_exclusive(v___x_2232_)) as u8;
                        if v_isSharedCheck_2263_ == 0 {
                            v___x_2258_ = v___x_2232_;
                            v_isShared_2259_ = v_isSharedCheck_2263_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2256_);
                            lean_inc(v_a_2255_);
                            lean_dec(v___x_2232_);
                            v___x_2258_ = lean_box(0);
                            v_isShared_2259_ = v_isSharedCheck_2263_;
                            state = 3;
                            continue;
                        }
                    }
                }
                2 => {
                    v_decl_2264_ = lean_ctor_get(v_code_2221_, 0);
                    lean_inc_ref(v_decl_2264_);
                    v_k_2265_ = lean_ctor_get(v_code_2221_, 1);
                    lean_inc_ref(v_k_2265_);
                    lean_dec_ref_known(v_code_2221_, 2);
                    v_value_2266_ = lean_ctor_get(v_decl_2264_, 4);
                    lean_inc_ref(v_value_2266_);
                    lean_dec_ref(v_decl_2264_);
                    lean_inc_ref(v_a_2222_);
                    v___x_2267_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(
                        v_value_2266_,
                        v_a_2222_,
                        v_a_2223_,
                    );
                    if lean_obj_tag(v___x_2267_) == 0 {
                        v_a_2268_ = lean_ctor_get(v___x_2267_, 1);
                        lean_inc(v_a_2268_);
                        lean_dec_ref_known(v___x_2267_, 2);
                        v_code_2221_ = v_k_2265_;
                        v_a_2223_ = v_a_2268_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_2265_);
                        lean_dec_ref(v_a_2222_);
                        return v___x_2267_;
                    }
                }
                3 => {
                    lean_dec_ref(v_a_2222_);
                    v_isSharedCheck_2277_ = (!lean_is_exclusive(v_code_2221_)) as u8;
                    if v_isSharedCheck_2277_ == 0 {
                        v_unused_2278_ = lean_ctor_get(v_code_2221_, 1);
                        lean_dec(v_unused_2278_);
                        v_unused_2279_ = lean_ctor_get(v_code_2221_, 0);
                        lean_dec(v_unused_2279_);
                        v___x_2271_ = v_code_2221_;
                        v_isShared_2272_ = v_isSharedCheck_2277_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_code_2221_);
                        v___x_2271_ = lean_box(0);
                        v_isShared_2272_ = v_isSharedCheck_2277_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_cases_2280_ = lean_ctor_get(v_code_2221_, 0);
                    lean_inc_ref(v_cases_2280_);
                    lean_dec_ref_known(v_code_2221_, 1);
                    v_alts_2281_ = lean_ctor_get(v_cases_2280_, 3);
                    lean_inc_ref(v_alts_2281_);
                    lean_dec_ref(v_cases_2280_);
                    v___x_2282_ = lean_unsigned_to_nat(0);
                    v___x_2283_ = lean_array_get_size(v_alts_2281_);
                    v___x_2284_ = lean_box(0);
                    v___x_2285_ = lean_nat_dec_lt(v___x_2282_, v___x_2283_);
                    if v___x_2285_ == 0 {
                        lean_dec_ref(v_alts_2281_);
                        lean_dec_ref(v_a_2222_);
                        v___x_2286_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2286_, 0, v___x_2284_);
                        lean_ctor_set(v___x_2286_, 1, v_a_2223_);
                        return v___x_2286_;
                    } else {
                        v___x_2287_ = lean_nat_dec_le(v___x_2283_, v___x_2283_);
                        if v___x_2287_ == 0 {
                            if v___x_2285_ == 0 {
                                lean_dec_ref(v_alts_2281_);
                                lean_dec_ref(v_a_2222_);
                                v___x_2288_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_2288_, 0, v___x_2284_);
                                lean_ctor_set(v___x_2288_, 1, v_a_2223_);
                                return v___x_2288_;
                            } else {
                                v___x_2289_ = 0usize;
                                v___x_2290_ = lean_usize_of_nat(v___x_2283_);
                                v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_2281_, v___x_2289_, v___x_2290_, v___x_2284_, v_a_2222_, v_a_2223_);
                                lean_dec_ref(v_a_2222_);
                                lean_dec_ref(v_alts_2281_);
                                return v___x_2291_;
                            }
                        } else {
                            v___x_2292_ = 0usize;
                            v___x_2293_ = lean_usize_of_nat(v___x_2283_);
                            v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_alts_2281_, v___x_2292_, v___x_2293_, v___x_2284_, v_a_2222_, v_a_2223_);
                            lean_dec_ref(v_a_2222_);
                            lean_dec_ref(v_alts_2281_);
                            return v___x_2294_;
                        }
                    }
                }
                _ => {
                    lean_dec_ref(v_a_2222_);
                    lean_dec_ref(v_code_2221_);
                    v___x_2295_ = lean_box(0);
                    v___x_2296_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2296_, 0, v___x_2295_);
                    lean_ctor_set(v___x_2296_, 1, v_a_2223_);
                    return v___x_2296_;
                }
            },
            1 => {
                v_fvarId_2239_ = lean_ctor_get(v_decl_2230_, 0);
                lean_inc(v_fvarId_2239_);
                lean_dec_ref(v_decl_2230_);
                v_decls_2240_ = lean_ctor_get(v_a_2222_, 0);
                lean_inc_ref(v_decls_2240_);
                v_main_2241_ = lean_ctor_get(v_a_2222_, 1);
                lean_inc_ref(v_main_2241_);
                v_assignment_2242_ = lean_ctor_get(v_a_2222_, 2);
                lean_inc(v_assignment_2242_);
                lean_dec_ref(v_a_2222_);
                if v_isShared_2238_ == 0 {
                    lean_ctor_set_tag(v___x_2237_, 2);
                    v___x_2244_ = v___x_2237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_val_2235_);
                    v___x_2244_ = v_reuseFailAlloc_2248_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2245_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_2239_, v___x_2244_, v_assignment_2242_);
                v___x_2246_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2246_, 0, v_decls_2240_);
                lean_ctor_set(v___x_2246_, 1, v_main_2241_);
                lean_ctor_set(v___x_2246_, 2, v___x_2245_);
                v_code_2221_ = v_k_2231_;
                v_a_2222_ = v___x_2246_;
                v_a_2223_ = v_a_2234_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2259_ == 0 {
                    v___x_2261_ = v___x_2258_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2255_);
                    lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_a_2256_);
                    v___x_2261_ = v_reuseFailAlloc_2262_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2261_;
            }
            5 => {
                v___x_2273_ = lean_box(0);
                if v_isShared_2272_ == 0 {
                    lean_ctor_set_tag(v___x_2271_, 0);
                    lean_ctor_set(v___x_2271_, 1, v_a_2223_);
                    lean_ctor_set(v___x_2271_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2271_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
                    lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_a_2223_);
                    v___x_2275_ = v_reuseFailAlloc_2276_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___lam__0(
    mut v_a_2297_: *mut LeanObject,
    mut v_a_2298_: *mut LeanObject,
    mut v_c_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_main_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    v_decls_2302_ = lean_ctor_get(v___y_2300_, 0);
    v_main_2303_ = lean_ctor_get(v___y_2300_, 1);
    v___x_2304_ = l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_2297_, v_a_2298_);
    lean_inc_ref(v_main_2303_);
    lean_inc_ref(v_decls_2302_);
    v___x_2305_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2305_, 0, v_decls_2302_);
    lean_ctor_set(v___x_2305_, 1, v_main_2303_);
    lean_ctor_set(v___x_2305_, 2, v___x_2304_);
    v___x_2306_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(v_c_2299_, v___x_2305_, v___y_2301_);
    return v___x_2306_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalLetValue___boxed(
    mut v_e_2307_: *mut LeanObject,
    mut v_a_2308_: *mut LeanObject,
    mut v_a_2309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2310_: *mut LeanObject = core::ptr::null_mut();
    v_res_2310_ = l_Lean_Compiler_LCNF_FixedParams_evalLetValue(v_e_2307_, v_a_2308_, v_a_2309_);
    lean_dec_ref(v_a_2308_);
    return v_res_2310_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9___boxed(
    mut v_as_2311_: *mut LeanObject,
    mut v_i_2312_: *mut LeanObject,
    mut v_stop_2313_: *mut LeanObject,
    mut v_b_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2317_: usize = 0;
    let mut v_stop_boxed_2318_: usize = 0;
    let mut v_res_2319_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2317_ = lean_unbox_usize(v_i_2312_);
    lean_dec(v_i_2312_);
    v_stop_boxed_2318_ = lean_unbox_usize(v_stop_2313_);
    lean_dec(v_stop_2313_);
    v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FixedParams_evalCode_spec__9(v_as_2311_, v_i_boxed_2317_, v_stop_boxed_2318_, v_b_2314_, v___y_2315_, v___y_2316_);
    lean_dec_ref(v___y_2315_);
    lean_dec_ref(v_as_2311_);
    return v_res_2319_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_evalApp___boxed(
    mut v_declName_2320_: *mut LeanObject,
    mut v_args_2321_: *mut LeanObject,
    mut v_a_2322_: *mut LeanObject,
    mut v_a_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2324_: *mut LeanObject = core::ptr::null_mut();
    v_res_2324_ = l_Lean_Compiler_LCNF_FixedParams_evalApp(
        v_declName_2320_,
        v_args_2321_,
        v_a_2322_,
        v_a_2323_,
    );
    lean_dec_ref(v_a_2322_);
    lean_dec_ref(v_args_2321_);
    return v_res_2324_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___boxed(
    mut v_declName_2325_: *mut LeanObject,
    mut v_args_2326_: *mut LeanObject,
    mut v_as_2327_: *mut LeanObject,
    mut v_sz_2328_: *mut LeanObject,
    mut v_i_2329_: *mut LeanObject,
    mut v_b_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2333_: usize = 0;
    let mut v_i_boxed_2334_: usize = 0;
    let mut v_res_2335_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2333_ = lean_unbox_usize(v_sz_2328_);
    lean_dec(v_sz_2328_);
    v_i_boxed_2334_ = lean_unbox_usize(v_i_2329_);
    lean_dec(v_i_2329_);
    v_res_2335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5(v_declName_2325_, v_args_2326_, v_as_2327_, v_sz_boxed_2333_, v_i_boxed_2334_, v_b_2330_, v___y_2331_, v___y_2332_);
    lean_dec_ref(v___y_2331_);
    lean_dec_ref(v_as_2327_);
    lean_dec_ref(v_args_2326_);
    return v_res_2335_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(
    mut v_pu_2336_: u8,
    mut v_f_2337_: *mut LeanObject,
    mut v_v_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    v___x_2341_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___redArg(v_f_2337_, v_v_2338_, v___y_2339_, v___y_2340_);
    return v___x_2341_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3___boxed(
    mut v_pu_2342_: *mut LeanObject,
    mut v_f_2343_: *mut LeanObject,
    mut v_v_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_2347_: u8 = 0;
    let mut v_res_2348_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_2347_ = (lean_unbox(v_pu_2342_) as u8);
    v_res_2348_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__3(v_pu_boxed_2347_, v_f_2343_, v_v_2344_, v___y_2345_, v___y_2346_);
    lean_dec_ref(v___y_2345_);
    return v_res_2348_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(
    mut v_00_u03b2_2349_: *mut LeanObject,
    mut v_m_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
) -> u8 {
    let mut v___x_2352_: u8 = 0;
    v___x_2352_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___redArg(v_m_2350_, v_a_2351_);
    return v___x_2352_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1___boxed(
    mut v_00_u03b2_2353_: *mut LeanObject,
    mut v_m_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2356_: u8 = 0;
    let mut v_r_2357_: *mut LeanObject = core::ptr::null_mut();
    v_res_2356_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1(v_00_u03b2_2353_, v_m_2354_, v_a_2355_);
    lean_dec_ref(v_a_2355_);
    lean_dec_ref(v_m_2354_);
    v_r_2357_ = lean_box((v_res_2356_) as usize);
    return v_r_2357_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2(
    mut v_00_u03b2_2358_: *mut LeanObject,
    mut v_m_2359_: *mut LeanObject,
    mut v_a_2360_: *mut LeanObject,
    mut v_b_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    v___x_2362_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2___redArg(v_m_2359_, v_a_2360_, v_b_2361_);
    return v___x_2362_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(
    mut v_upperBound_2363_: *mut LeanObject,
    mut v_args_2364_: *mut LeanObject,
    mut v_inst_2365_: *mut LeanObject,
    mut v_R_2366_: *mut LeanObject,
    mut v_a_2367_: *mut LeanObject,
    mut v_b_2368_: *mut LeanObject,
    mut v_c_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    v___x_2372_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___redArg(v_upperBound_2363_, v_args_2364_, v_a_2367_, v_b_2368_, v___y_2370_, v___y_2371_);
    return v___x_2372_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4___boxed(
    mut v_upperBound_2373_: *mut LeanObject,
    mut v_args_2374_: *mut LeanObject,
    mut v_inst_2375_: *mut LeanObject,
    mut v_R_2376_: *mut LeanObject,
    mut v_a_2377_: *mut LeanObject,
    mut v_b_2378_: *mut LeanObject,
    mut v_c_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2382_: *mut LeanObject = core::ptr::null_mut();
    v_res_2382_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__4(
            v_upperBound_2373_,
            v_args_2374_,
            v_inst_2375_,
            v_R_2376_,
            v_a_2377_,
            v_b_2378_,
            v_c_2379_,
            v___y_2380_,
            v___y_2381_,
        );
    lean_dec_ref(v___y_2380_);
    lean_dec_ref(v_args_2374_);
    lean_dec(v_upperBound_2373_);
    return v_res_2382_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(
    mut v_upperBound_2383_: *mut LeanObject,
    mut v_args_2384_: *mut LeanObject,
    mut v_inst_2385_: *mut LeanObject,
    mut v_R_2386_: *mut LeanObject,
    mut v_a_2387_: *mut LeanObject,
    mut v_b_2388_: *mut LeanObject,
    mut v_c_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___redArg(v_upperBound_2383_, v_args_2384_, v_a_2387_, v_b_2388_, v___y_2390_, v___y_2391_);
    return v___x_2392_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7___boxed(
    mut v_upperBound_2393_: *mut LeanObject,
    mut v_args_2394_: *mut LeanObject,
    mut v_inst_2395_: *mut LeanObject,
    mut v_R_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_b_2398_: *mut LeanObject,
    mut v_c_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2402_: *mut LeanObject = core::ptr::null_mut();
    v_res_2402_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__7(
            v_upperBound_2393_,
            v_args_2394_,
            v_inst_2395_,
            v_R_2396_,
            v_a_2397_,
            v_b_2398_,
            v_c_2399_,
            v___y_2400_,
            v___y_2401_,
        );
    lean_dec_ref(v___y_2400_);
    lean_dec_ref(v_args_2394_);
    lean_dec(v_upperBound_2393_);
    return v_res_2402_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(
    mut v_00_u03b2_2403_: *mut LeanObject,
    mut v_a_2404_: *mut LeanObject,
    mut v_x_2405_: *mut LeanObject,
) -> u8 {
    let mut v___x_2406_: u8 = 0;
    v___x_2406_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___redArg(v_a_2404_, v_x_2405_);
    return v___x_2406_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1___boxed(
    mut v_00_u03b2_2407_: *mut LeanObject,
    mut v_a_2408_: *mut LeanObject,
    mut v_x_2409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2410_: u8 = 0;
    let mut v_r_2411_: *mut LeanObject = core::ptr::null_mut();
    v_res_2410_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1(v_00_u03b2_2407_, v_a_2408_, v_x_2409_);
    lean_dec(v_x_2409_);
    lean_dec_ref(v_a_2408_);
    v_r_2411_ = lean_box((v_res_2410_) as usize);
    return v_r_2411_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4(
    mut v_00_u03b2_2412_: *mut LeanObject,
    mut v_data_2413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    v___x_2414_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4___redArg(v_data_2413_);
    return v___x_2414_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(
    mut v_xs_2415_: *mut LeanObject,
    mut v_ys_2416_: *mut LeanObject,
    mut v_hsz_2417_: *mut LeanObject,
    mut v_x_2418_: *mut LeanObject,
    mut v_x_2419_: *mut LeanObject,
) -> u8 {
    let mut v___x_2420_: u8 = 0;
    v___x_2420_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___redArg(v_xs_2415_, v_ys_2416_, v_x_2418_);
    return v___x_2420_;
}
pub unsafe fn l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4___boxed(
    mut v_xs_2421_: *mut LeanObject,
    mut v_ys_2422_: *mut LeanObject,
    mut v_hsz_2423_: *mut LeanObject,
    mut v_x_2424_: *mut LeanObject,
    mut v_x_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2426_: u8 = 0;
    let mut v_r_2427_: *mut LeanObject = core::ptr::null_mut();
    v_res_2426_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__1_spec__1_spec__4(v_xs_2421_, v_ys_2422_, v_hsz_2423_, v_x_2424_, v_x_2425_);
    lean_dec_ref(v_ys_2422_);
    lean_dec_ref(v_xs_2421_);
    v_r_2427_ = lean_box((v_res_2426_) as usize);
    return v_r_2427_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8(
    mut v_00_u03b2_2428_: *mut LeanObject,
    mut v_i_2429_: *mut LeanObject,
    mut v_source_2430_: *mut LeanObject,
    mut v_target_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    v___x_2432_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8___redArg(v_i_2429_, v_source_2430_, v_target_2431_);
    return v___x_2432_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14(
    mut v_00_u03b2_2433_: *mut LeanObject,
    mut v_x_2434_: *mut LeanObject,
    mut v_x_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    v___x_2436_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__2_spec__4_spec__8_spec__14___redArg(v_x_2434_, v_x_2435_);
    return v___x_2436_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(
    mut v_upperBound_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
    mut v_b_2439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2440_: u8 = 0;
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2440_ = lean_nat_dec_lt(v_a_2438_, v_upperBound_2437_);
                if v___x_2440_ == 0 {
                    lean_dec(v_a_2438_);
                    return v_b_2439_;
                } else {
                    lean_inc(v_a_2438_);
                    v___x_2441_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_2441_, 0, v_a_2438_);
                    v___x_2442_ = lean_array_push(v_b_2439_, v___x_2441_);
                    v___x_2443_ = lean_unsigned_to_nat(1);
                    v___x_2444_ = lean_nat_add(v_a_2438_, v___x_2443_);
                    lean_dec(v_a_2438_);
                    v_a_2438_ = v___x_2444_;
                    v_b_2439_ = v___x_2442_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg___boxed(
    mut v_upperBound_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
    mut v_b_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_2446_, v_a_2447_, v_b_2448_);
    lean_dec(v_upperBound_2446_);
    return v_res_2449_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(
    mut v_numParams_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    v___x_2451_ = lean_unsigned_to_nat(0);
    v_values_2452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FixedParams_evalApp_spec__5___closed__0;
    v___x_2453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_numParams_2450_, v___x_2451_, v_values_2452_);
    return v___x_2453_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FixedParams_mkInitialValues___boxed(
    mut v_numParams_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2455_: *mut LeanObject = core::ptr::null_mut();
    v_res_2455_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v_numParams_2454_);
    lean_dec(v_numParams_2454_);
    return v_res_2455_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(
    mut v_upperBound_2456_: *mut LeanObject,
    mut v_inst_2457_: *mut LeanObject,
    mut v_R_2458_: *mut LeanObject,
    mut v_a_2459_: *mut LeanObject,
    mut v_b_2460_: *mut LeanObject,
    mut v_c_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___redArg(v_upperBound_2456_, v_a_2459_, v_b_2460_);
    return v___x_2462_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0___boxed(
    mut v_upperBound_2463_: *mut LeanObject,
    mut v_inst_2464_: *mut LeanObject,
    mut v_R_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
    mut v_b_2467_: *mut LeanObject,
    mut v_c_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2469_: *mut LeanObject = core::ptr::null_mut();
    v_res_2469_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FixedParams_mkInitialValues_spec__0(v_upperBound_2463_, v_inst_2464_, v_R_2465_, v_a_2466_, v_b_2467_, v_c_2468_);
    lean_dec(v_upperBound_2463_);
    return v_res_2469_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    v___x_2470_ = lean_box(0);
    v___x_2471_ = lean_unsigned_to_nat(16);
    v___x_2472_ = lean_mk_array(v___x_2471_, v___x_2470_);
    return v___x_2472_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2473_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__0);
    v___x_2474_ = lean_unsigned_to_nat(0);
    v___x_2475_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2475_, 0, v___x_2474_);
    lean_ctor_set(v___x_2475_, 1, v___x_2473_);
    return v___x_2475_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(
    mut v_decls_2476_: *mut LeanObject,
    mut v_as_2477_: *mut LeanObject,
    mut v_sz_2478_: usize,
    mut v_i_2479_: usize,
    mut v_b_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: usize = 0;
    let mut v___x_2484_: usize = 0;
    let mut v___x_2486_: u8 = 0;
    let mut v_a_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixed_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2486_ = lean_usize_dec_lt(v_i_2479_, v_sz_2478_);
                if v___x_2486_ == 0 {
                    lean_dec_ref(v_decls_2476_);
                    return v_b_2480_;
                } else {
                    v_a_2487_ = lean_array_uget_borrowed(v_as_2477_, v_i_2479_);
                    v_toSignature_2488_ = lean_ctor_get(v_a_2487_, 0);
                    v_value_2489_ = lean_ctor_get(v_a_2487_, 1);
                    v_name_2490_ = lean_ctor_get(v_toSignature_2488_, 0);
                    v_params_2491_ = lean_ctor_get(v_toSignature_2488_, 3);
                    v___x_2496_ = lean_array_get_size(v_params_2491_);
                    v___x_2497_ = l_Lean_Compiler_LCNF_FixedParams_mkInitialValues(v___x_2496_);
                    v___x_2498_ = lean_box((v___x_2486_) as usize);
                    v___x_2499_ = lean_mk_array(v___x_2496_, v___x_2498_);
                    if lean_obj_tag(v_value_2489_) == 0 {
                        v_code_2500_ = lean_ctor_get(v_value_2489_, 0);
                        v___x_2501_ =
                            l_Lean_Compiler_LCNF_FixedParams_mkAssignment(v_a_2487_, v___x_2497_);
                        lean_inc(v_a_2487_);
                        lean_inc_ref(v_decls_2476_);
                        v___x_2502_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_2502_, 0, v_decls_2476_);
                        lean_ctor_set(v___x_2502_, 1, v_a_2487_);
                        lean_ctor_set(v___x_2502_, 2, v___x_2501_);
                        v___x_2503_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___closed__1);
                        v___x_2504_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2504_, 0, v___x_2503_);
                        lean_ctor_set(v___x_2504_, 1, v___x_2499_);
                        lean_inc_ref(v_code_2500_);
                        v___x_2505_ = l_Lean_Compiler_LCNF_FixedParams_evalCode(
                            v_code_2500_,
                            v___x_2502_,
                            v___x_2504_,
                        );
                        v_a_2506_ = lean_ctor_get(v___x_2505_, 1);
                        lean_inc(v_a_2506_);
                        lean_dec_ref(v___x_2505_);
                        v_s_2493_ = v_a_2506_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v___x_2497_);
                        lean_inc(v_name_2490_);
                        v___x_2507_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2490_, v___x_2499_, v_b_2480_);
                        v_a_2482_ = v___x_2507_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2483_ = 1usize;
                v___x_2484_ = lean_usize_add(v_i_2479_, v___x_2483_);
                v_i_2479_ = v___x_2484_;
                v_b_2480_ = v_a_2482_;
                state = 0;
                continue;
            }
            2 => {
                v_fixed_2494_ = lean_ctor_get(v_s_2493_, 1);
                lean_inc_ref(v_fixed_2494_);
                lean_dec_ref(v_s_2493_);
                lean_inc(v_name_2490_);
                v___x_2495_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2490_, v_fixed_2494_, v_b_2480_);
                v_a_2482_ = v___x_2495_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0___boxed(
    mut v_decls_2508_: *mut LeanObject,
    mut v_as_2509_: *mut LeanObject,
    mut v_sz_2510_: *mut LeanObject,
    mut v_i_2511_: *mut LeanObject,
    mut v_b_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2513_: usize = 0;
    let mut v_i_boxed_2514_: usize = 0;
    let mut v_res_2515_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2513_ = lean_unbox_usize(v_sz_2510_);
    lean_dec(v_sz_2510_);
    v_i_boxed_2514_ = lean_unbox_usize(v_i_2511_);
    lean_dec(v_i_2511_);
    v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_2508_, v_as_2509_, v_sz_boxed_2513_, v_i_boxed_2514_, v_b_2512_);
    lean_dec_ref(v_as_2509_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_Compiler_LCNF_mkFixedParamsMap(
    mut v_decls_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_result_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2518_: usize = 0;
    let mut v___x_2519_: usize = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    v_result_2517_ = lean_box(1);
    v_sz_2518_ = lean_array_size(v_decls_2516_);
    v___x_2519_ = 0usize;
    lean_inc_ref(v_decls_2516_);
    v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_mkFixedParamsMap_spec__0(v_decls_2516_, v_decls_2516_, v_sz_2518_, v___x_2519_, v_result_2517_);
    lean_dec_ref(v_decls_2516_);
    return v___x_2520_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_FixedParams(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default =
        _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default();
    lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue_default);
    l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue =
        _init_l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue();
    lean_mark_persistent(l_Lean_Compiler_LCNF_FixedParams_instInhabitedAbsValue);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_FixedParams(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_FixedParams(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_FixedParams(builtin);
}
