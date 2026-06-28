// Lean compiler output
// Module: Lean.Compiler.IR.Basic
// Imports: Lean.Compiler.ExternAttr Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::ExternAttr::{
    initialize_Lean_Compiler_ExternAttr, runtime_initialize_Lean_Compiler_ExternAttr,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_length,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_apply_6, lean_box,
    lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static mut l_Lean_IR_instInhabitedVarId_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_IR_instInhabitedVarId: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_instBEqVarId___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instBEqVarId_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instBEqVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instBEqVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqVarId___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instHashableVarId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instHashableVarId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instHashableVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instHashableVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableVarId___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__0_value: LeanStringObject<3> =
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
        m_data: [123, 32, 0],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__1_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 100, 120, 0],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__4_value: LeanStringObject<5> =
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
        m_data: [32, 58, 61, 32, 0],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__8_value: LeanStringObject<3> =
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
        m_data: [32, 125, 0],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprVarId___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instReprVarId_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instReprVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instReprVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedJoinPointId_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_IR_instInhabitedJoinPointId: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_instBEqJoinPointId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instBEqJoinPointId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqJoinPointId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqJoinPointId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instBEqJoinPointId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqJoinPointId___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instHashableJoinPointId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instHashableJoinPointId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instHashableJoinPointId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableJoinPointId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instHashableJoinPointId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableJoinPointId___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprJoinPointId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instReprJoinPointId_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instReprJoinPointId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprJoinPointId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instReprJoinPointId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprJoinPointId___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringVarId___lam__0___closed__0_value: LeanStringObject<3> =
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
        m_data: [120, 95, 0],
    };
static mut l_Lean_IR_instToStringVarId___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringVarId___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringVarId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToStringVarId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToStringVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringVarId___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instToStringJoinPointId___lam__0___closed__0_value: LeanStringObject<7> =
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
        m_data: [98, 108, 111, 99, 107, 95, 0],
    };
static mut l_Lean_IR_instToStringJoinPointId___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringJoinPointId___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_instToStringJoinPointId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_instToStringJoinPointId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringJoinPointId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringJoinPointId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instToStringJoinPointId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringJoinPointId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedIRType_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_IR_instInhabitedIRType: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_instBEqIRType___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instBEqIRType_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instBEqIRType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqIRType___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instBEqIRType: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqIRType___closed__0_value) as *mut LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value
)
    as *mut LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1_value
)
    as *mut LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value
)
    as *mut LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3_value
)
    as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 102, 108, 111, 97,
            116, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__2_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 105, 110, 116,
            56, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__4_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 105, 110, 116,
            49, 54, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__5_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__6_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 105, 110, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__6_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__7_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__8_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 105, 110, 116,
            54, 52, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__8_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__9_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__10_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 115, 105, 122,
            101, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__10_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__11_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__11_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__12_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 101, 114, 97, 115,
            101, 100, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__12_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__13_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__12_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__13_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__14_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 111, 98, 106, 101, 99,
            116, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__14_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__15_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__15_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__16_value: LeanStringObject<23> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 116, 111, 98, 106,
            101, 99, 116, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__16_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__17_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__17_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__18_value: LeanStringObject<23> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 102, 108, 111, 97,
            116, 51, 50, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__18_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__19_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__19_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__20_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 116, 97, 103, 103,
            101, 100, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__20_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__21_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__20_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__21_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__22_value: LeanStringObject<20> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 118, 111, 105, 100, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__22_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__23_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__22_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__23_value) as *mut LeanObject;
static mut l_Lean_IR_instReprIRType_repr___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprIRType_repr___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_IR_instReprIRType_repr___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprIRType_repr___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_instReprIRType_repr___closed__26_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 115, 116, 114, 117,
            99, 116, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__26_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__27_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__26_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__27_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__28_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__27_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__28_value) as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value)
        as *mut LeanObject;
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value
    ) as *mut LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10_value
)
    as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__29_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 110, 105, 111,
            110, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__29_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__30_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__29_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__30_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__31_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__30_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprIRType_repr___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__31_value) as *mut LeanObject;
pub static l_Lean_IR_instReprIRType___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instReprIRType_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instReprIRType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instReprIRType: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedArg_default___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
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
static mut l_Lean_IR_instInhabitedArg_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedArg_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedArg_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedArg_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedArg_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instBEqArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instBEqArg_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instBEqArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instBEqArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__0_value: LeanStringObject<19> = LeanStringObject {
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
        76, 101, 97, 110, 46, 73, 82, 46, 65, 114, 103, 46, 101, 114, 97, 115, 101, 100, 0,
    ],
};
static mut l_Lean_IR_instReprArg_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_IR_instReprArg_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__2_value: LeanStringObject<16> = LeanStringObject {
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
        76, 101, 97, 110, 46, 73, 82, 46, 65, 114, 103, 46, 118, 97, 114, 0,
    ],
};
static mut l_Lean_IR_instReprArg_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_IR_instReprArg_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__4_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__3_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_instReprArg_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_instReprArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instReprArg_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instReprArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instReprArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedLitVal_default___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
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
static mut l_Lean_IR_instInhabitedLitVal_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedLitVal_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedLitVal_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedLitVal_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedLitVal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedLitVal_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instBEqLitVal___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instBEqLitVal_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instBEqLitVal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqLitVal___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instBEqLitVal: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqLitVal___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value: LeanCtorObject<5> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedCtorInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedCtorInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedCtorInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_instBEqCtorInfo___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instBEqCtorInfo_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instBEqCtorInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqCtorInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instBEqCtorInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqCtorInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value: LeanStringObject<5> =
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
        m_data: [110, 97, 109, 101, 0],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value: LeanStringObject<5> =
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
        m_data: [99, 105, 100, 120, 0],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value: LeanStringObject<5> =
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
        m_data: [115, 105, 122, 101, 0],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value: LeanStringObject<6> =
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
        m_data: [117, 115, 105, 122, 101, 0],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value: LeanStringObject<6> =
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
        m_data: [115, 115, 105, 122, 101, 0],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_IR_instReprCtorInfo___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instReprCtorInfo_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instReprCtorInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instReprCtorInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedExpr_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_IR_instInhabitedExpr_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedExpr_default___closed__1_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedExpr_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedExpr_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedParam_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedParam_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedParam_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedParam_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedParam_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedParam: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedParam_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [120, 0],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__3_value) as *mut LeanObject;
static mut l_Lean_IR_instReprParam_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprParam_repr___redArg___closed__5_value: LeanStringObject<7> =
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
        m_data: [98, 111, 114, 114, 111, 119, 0],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_IR_instReprParam_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprParam_repr___redArg___closed__8_value: LeanStringObject<3> =
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
        m_data: [116, 121, 0],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__9_value) as *mut LeanObject;
static mut l_Lean_IR_instReprParam_repr___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprParam___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_instReprParam_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instReprParam___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instReprParam: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_IR_instInhabitedFnBody_default__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 9,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedFnBody_default__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedFnBody_default__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedFnBody: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_IR_instInhabitedAlt_default__1___closed__0_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedAlt_default__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedAlt_default__1___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedAlt_default__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedAlt_default__1___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedAlt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedAlt_default__1___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_FnBody_nil: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_Alt_modifyBodyM___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_Alt_modifyBodyM___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_Alt_modifyBodyM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_FnBody_flatten___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_IR_FnBody_flatten___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_FnBody_flatten___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_reshapeAux___closed__0_value: LeanStringObject<22> = LeanStringObject {
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
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 65, 114, 114, 97, 121, 46, 66, 97, 115, 105,
        99, 0,
    ],
};
static mut l_Lean_IR_reshapeAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_reshapeAux___closed__1_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [65, 114, 114, 97, 121, 46, 115, 119, 97, 112, 65, 116, 33, 0],
};
static mut l_Lean_IR_reshapeAux___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_reshapeAux___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 110, 100, 101, 120, 32, 0],
};
static mut l_Lean_IR_reshapeAux___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_reshapeAux___closed__3_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 0,
    ],
};
static mut l_Lean_IR_reshapeAux___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lean_IR_modifyJPs___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lean_IR_modifyJPs___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lean_IR_modifyJPs___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lean_IR_modifyJPs___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lean_IR_modifyJPs___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lean_IR_modifyJPs___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__5_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_Lean_IR_modifyJPs___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__6_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_modifyJPs___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__7_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_modifyJPs___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__8_value) as *mut LeanObject;
pub static l_Lean_IR_modifyJPs___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_modifyJPs___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__9_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedDecl_default___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_IR_instInhabitedDecl_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instInhabitedDecl_default___closed__1_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedDecl_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedDecl_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_IR_instInhabitedDecl: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_Decl_updateBody_x21___closed__0_value: LeanStringObject<23> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 73, 82, 46, 66, 97,
            115, 105, 99, 0,
        ],
    };
static mut l_Lean_IR_Decl_updateBody_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Decl_updateBody_x21___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_Decl_updateBody_x21___closed__1_value: LeanStringObject<25> =
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
            76, 101, 97, 110, 46, 73, 82, 46, 68, 101, 99, 108, 46, 117, 112, 100, 97, 116, 101,
            66, 111, 100, 121, 33, 0,
        ],
    };
static mut l_Lean_IR_Decl_updateBody_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Decl_updateBody_x21___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_Decl_updateBody_x21___closed__2_value: LeanStringObject<20> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111,
            110, 0,
        ],
    };
static mut l_Lean_IR_Decl_updateBody_x21___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Decl_updateBody_x21___closed__2_value) as *mut LeanObject;
static mut l_Lean_IR_Decl_updateBody_x21___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_IR_Decl_updateBody_x21___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_instAlphaEqvVarId___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_VarId_alphaEqv___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instAlphaEqvVarId___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvVarId___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instAlphaEqvVarId: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvVarId___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instAlphaEqvArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_Arg_alphaEqv___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instAlphaEqvArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instAlphaEqvArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instAlphaEqvArrayArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_IR_args_alphaEqv___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instAlphaEqvArrayArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArrayArg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instAlphaEqvArrayArg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArrayArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instAlphaEqvExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_Expr_alphaEqv___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instAlphaEqvExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instAlphaEqvExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_instBEqFnBody___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_FnBody_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_instBEqFnBody___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqFnBody___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_IR_instBEqFnBody: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqFnBody___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_mkIf___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_IR_mkIf___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_mkIf___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
static mut l_Lean_IR_mkIf___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_mkIf___closed__2_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_IR_mkIf___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__2_value) as *mut LeanObject;
static l_Lean_IR_mkIf___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Lean_IR_mkIf___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__2_value) as *mut LeanObject,
        15761733860085307253 as *mut LeanObject,
    ],
};
static mut l_Lean_IR_mkIf___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_mkIf___closed__4_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__3_value) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_mkIf___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_mkIf___closed__5_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_IR_mkIf___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__5_value) as *mut LeanObject;
static l_Lean_IR_mkIf___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Lean_IR_mkIf___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__6_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__5_value) as *mut LeanObject,
        9255189395584251158 as *mut LeanObject,
    ],
};
static mut l_Lean_IR_mkIf___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__6_value) as *mut LeanObject;
pub static l_Lean_IR_mkIf___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_mkIf___closed__6_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_IR_mkIf___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__7_value) as *mut LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__0_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        108, 101, 97, 110, 95, 117, 110, 98, 111, 120, 95, 117, 115, 105, 122, 101, 0,
    ],
};
static mut l_Lean_IR_getUnboxOpName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__0_value) as *mut LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__1_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        108, 101, 97, 110, 95, 117, 110, 98, 111, 120, 95, 117, 105, 110, 116, 51, 50, 0,
    ],
};
static mut l_Lean_IR_getUnboxOpName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__1_value) as *mut LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__2_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        108, 101, 97, 110, 95, 117, 110, 98, 111, 120, 95, 117, 105, 110, 116, 54, 52, 0,
    ],
};
static mut l_Lean_IR_getUnboxOpName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__2_value) as *mut LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__3_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        108, 101, 97, 110, 95, 117, 110, 98, 111, 120, 95, 102, 108, 111, 97, 116, 0,
    ],
};
static mut l_Lean_IR_getUnboxOpName___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__3_value) as *mut LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__4_value: LeanStringObject<19> = LeanStringObject {
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
        108, 101, 97, 110, 95, 117, 110, 98, 111, 120, 95, 102, 108, 111, 97, 116, 51, 50, 0,
    ],
};
static mut l_Lean_IR_getUnboxOpName___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__4_value) as *mut LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__5_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [108, 101, 97, 110, 95, 117, 110, 98, 111, 120, 0],
};
static mut l_Lean_IR_getUnboxOpName___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__5_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_IR_instInhabitedVarId_default() -> *mut LeanObject {
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    v___x_3852_ = lean_unsigned_to_nat(0);
    return v___x_3852_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedVarId() -> *mut LeanObject {
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    v___x_3853_ = lean_unsigned_to_nat(0);
    return v___x_3853_;
}
pub unsafe fn l_Lean_IR_instBEqVarId_beq(
    mut v_x_3854_: *mut LeanObject,
    mut v_x_3855_: *mut LeanObject,
) -> u8 {
    let mut v___x_3856_: u8 = 0;
    v___x_3856_ = lean_nat_dec_eq(v_x_3854_, v_x_3855_);
    return v___x_3856_;
}
pub unsafe fn l_Lean_IR_instBEqVarId_beq___boxed(
    mut v_x_3857_: *mut LeanObject,
    mut v_x_3858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3859_: u8 = 0;
    let mut v_r_3860_: *mut LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Lean_IR_instBEqVarId_beq(v_x_3857_, v_x_3858_);
    lean_dec(v_x_3858_);
    lean_dec(v_x_3857_);
    v_r_3860_ = lean_box((v_res_3859_) as usize);
    return v_r_3860_;
}
pub unsafe fn l_Lean_IR_instHashableVarId_hash(mut v_x_3863_: *mut LeanObject) -> u64 {
    let mut v___x_3864_: u64 = 0;
    let mut v___x_3865_: u64 = 0;
    let mut v___x_3866_: u64 = 0;
    v___x_3864_ = 0u64;
    v___x_3865_ = lean_uint64_of_nat(v_x_3863_);
    v___x_3866_ = lean_uint64_mix_hash(v___x_3864_, v___x_3865_);
    return v___x_3866_;
}
pub unsafe fn l_Lean_IR_instHashableVarId_hash___boxed(
    mut v_x_3867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3868_: u64 = 0;
    let mut v_r_3869_: *mut LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Lean_IR_instHashableVarId_hash(v_x_3867_);
    lean_dec(v_x_3867_);
    v_r_3869_ = lean_box_uint64(v_res_3868_);
    return v_r_3869_;
}
pub unsafe fn l_Nat_cast___at___00Lean_IR_instReprVarId_repr_spec__0(
    mut v_a_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    v___x_3873_ = lean_nat_to_int(v_a_3872_);
    return v___x_3873_;
}
pub unsafe fn _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    v___x_3887_ = lean_unsigned_to_nat(7);
    v___x_3888_ = lean_nat_to_int(v___x_3887_);
    return v___x_3888_;
}
pub unsafe fn _init_l_Lean_IR_instReprVarId_repr___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    v___x_3890_ = l_Lean_IR_instReprVarId_repr___redArg___closed__0;
    v___x_3891_ = lean_string_length(v___x_3890_);
    return v___x_3891_;
}
pub unsafe fn _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    v___x_3892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__9_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__9,
    );
    v___x_3893_ = lean_nat_to_int(v___x_3892_);
    return v___x_3893_;
}
pub unsafe fn l_Lean_IR_instReprVarId_repr___redArg(
    mut v_x_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_Lean_IR_instReprVarId_repr___redArg___closed__6;
    v___x_3900_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7,
    );
    v___x_3901_ = l_Nat_reprFast(v_x_3898_);
    v___x_3902_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3902_, 0, v___x_3901_);
    v___x_3903_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3903_, 0, v___x_3900_);
    lean_ctor_set(v___x_3903_, 1, v___x_3902_);
    v___x_3904_ = 0;
    v___x_3905_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3905_, 0, v___x_3903_);
    lean_ctor_set_uint8(
        v___x_3905_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3904_,
    );
    v___x_3906_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3906_, 0, v___x_3899_);
    lean_ctor_set(v___x_3906_, 1, v___x_3905_);
    v___x_3907_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_3908_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_3909_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3909_, 0, v___x_3908_);
    lean_ctor_set(v___x_3909_, 1, v___x_3906_);
    v___x_3910_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_3911_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3911_, 0, v___x_3909_);
    lean_ctor_set(v___x_3911_, 1, v___x_3910_);
    v___x_3912_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3912_, 0, v___x_3907_);
    lean_ctor_set(v___x_3912_, 1, v___x_3911_);
    v___x_3913_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3913_, 0, v___x_3912_);
    lean_ctor_set_uint8(
        v___x_3913_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3904_,
    );
    return v___x_3913_;
}
pub unsafe fn l_Lean_IR_instReprVarId_repr(
    mut v_x_3914_: *mut LeanObject,
    mut v_prec_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    v___x_3916_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_3914_);
    return v___x_3916_;
}
pub unsafe fn l_Lean_IR_instReprVarId_repr___boxed(
    mut v_x_3917_: *mut LeanObject,
    mut v_prec_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3919_: *mut LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Lean_IR_instReprVarId_repr(v_x_3917_, v_prec_3918_);
    lean_dec(v_prec_3918_);
    return v_res_3919_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedJoinPointId_default() -> *mut LeanObject {
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    v___x_3922_ = lean_unsigned_to_nat(0);
    return v___x_3922_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedJoinPointId() -> *mut LeanObject {
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    v___x_3923_ = lean_unsigned_to_nat(0);
    return v___x_3923_;
}
pub unsafe fn l_Lean_IR_instBEqJoinPointId_beq(
    mut v_x_3924_: *mut LeanObject,
    mut v_x_3925_: *mut LeanObject,
) -> u8 {
    let mut v___x_3926_: u8 = 0;
    v___x_3926_ = lean_nat_dec_eq(v_x_3924_, v_x_3925_);
    return v___x_3926_;
}
pub unsafe fn l_Lean_IR_instBEqJoinPointId_beq___boxed(
    mut v_x_3927_: *mut LeanObject,
    mut v_x_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3929_: u8 = 0;
    let mut v_r_3930_: *mut LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_Lean_IR_instBEqJoinPointId_beq(v_x_3927_, v_x_3928_);
    lean_dec(v_x_3928_);
    lean_dec(v_x_3927_);
    v_r_3930_ = lean_box((v_res_3929_) as usize);
    return v_r_3930_;
}
pub unsafe fn l_Lean_IR_instHashableJoinPointId_hash(mut v_x_3933_: *mut LeanObject) -> u64 {
    let mut v___x_3934_: u64 = 0;
    let mut v___x_3935_: u64 = 0;
    let mut v___x_3936_: u64 = 0;
    v___x_3934_ = 0u64;
    v___x_3935_ = lean_uint64_of_nat(v_x_3933_);
    v___x_3936_ = lean_uint64_mix_hash(v___x_3934_, v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn l_Lean_IR_instHashableJoinPointId_hash___boxed(
    mut v_x_3937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3938_: u64 = 0;
    let mut v_r_3939_: *mut LeanObject = core::ptr::null_mut();
    v_res_3938_ = l_Lean_IR_instHashableJoinPointId_hash(v_x_3937_);
    lean_dec(v_x_3937_);
    v_r_3939_ = lean_box_uint64(v_res_3938_);
    return v_r_3939_;
}
pub unsafe fn l_Lean_IR_instReprJoinPointId_repr___redArg(
    mut v_x_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: u8 = 0;
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_IR_instReprVarId_repr___redArg___closed__6;
    v___x_3944_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7,
    );
    v___x_3945_ = l_Nat_reprFast(v_x_3942_);
    v___x_3946_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3946_, 0, v___x_3945_);
    v___x_3947_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3947_, 0, v___x_3944_);
    lean_ctor_set(v___x_3947_, 1, v___x_3946_);
    v___x_3948_ = 0;
    v___x_3949_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3949_, 0, v___x_3947_);
    lean_ctor_set_uint8(
        v___x_3949_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3948_,
    );
    v___x_3950_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3950_, 0, v___x_3943_);
    lean_ctor_set(v___x_3950_, 1, v___x_3949_);
    v___x_3951_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_3952_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_3953_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3953_, 0, v___x_3952_);
    lean_ctor_set(v___x_3953_, 1, v___x_3950_);
    v___x_3954_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_3955_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3955_, 0, v___x_3953_);
    lean_ctor_set(v___x_3955_, 1, v___x_3954_);
    v___x_3956_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3956_, 0, v___x_3951_);
    lean_ctor_set(v___x_3956_, 1, v___x_3955_);
    v___x_3957_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3957_, 0, v___x_3956_);
    lean_ctor_set_uint8(
        v___x_3957_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3948_,
    );
    return v___x_3957_;
}
pub unsafe fn l_Lean_IR_instReprJoinPointId_repr(
    mut v_x_3958_: *mut LeanObject,
    mut v_prec_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_IR_instReprJoinPointId_repr___redArg(v_x_3958_);
    return v___x_3960_;
}
pub unsafe fn l_Lean_IR_instReprJoinPointId_repr___boxed(
    mut v_x_3961_: *mut LeanObject,
    mut v_prec_3962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3963_: *mut LeanObject = core::ptr::null_mut();
    v_res_3963_ = l_Lean_IR_instReprJoinPointId_repr(v_x_3961_, v_prec_3962_);
    lean_dec(v_prec_3962_);
    return v_res_3963_;
}
pub unsafe fn l_Lean_IR_Index_lt(
    mut v_a_3966_: *mut LeanObject,
    mut v_b_3967_: *mut LeanObject,
) -> u8 {
    let mut v___x_3968_: u8 = 0;
    v___x_3968_ = lean_nat_dec_lt(v_a_3966_, v_b_3967_);
    return v___x_3968_;
}
pub unsafe fn l_Lean_IR_Index_lt___boxed(
    mut v_a_3969_: *mut LeanObject,
    mut v_b_3970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3971_: u8 = 0;
    let mut v_r_3972_: *mut LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Lean_IR_Index_lt(v_a_3969_, v_b_3970_);
    lean_dec(v_b_3970_);
    lean_dec(v_a_3969_);
    v_r_3972_ = lean_box((v_res_3971_) as usize);
    return v_r_3972_;
}
pub unsafe fn l_Lean_IR_instToStringVarId___lam__0(
    mut v_a_3974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    v___x_3975_ = l_Lean_IR_instToStringVarId___lam__0___closed__0;
    v___x_3976_ = l_Nat_reprFast(v_a_3974_);
    v___x_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
    lean_dec_ref(v___x_3976_);
    return v___x_3977_;
}
pub unsafe fn l_Lean_IR_instToStringJoinPointId___lam__0(
    mut v_a_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    v___x_3982_ = l_Lean_IR_instToStringJoinPointId___lam__0___closed__0;
    v___x_3983_ = l_Nat_reprFast(v_a_3981_);
    v___x_3984_ = lean_string_append(v___x_3982_, v___x_3983_);
    lean_dec_ref(v___x_3983_);
    return v___x_3984_;
}
pub unsafe fn l_Lean_IR_IRType_ctorIdx(mut v_x_3987_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_3987_) {
        0 => {
            let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
            v___x_3988_ = lean_unsigned_to_nat(0);
            return v___x_3988_;
        }
        1 => {
            let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
            v___x_3989_ = lean_unsigned_to_nat(1);
            return v___x_3989_;
        }
        2 => {
            let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
            v___x_3990_ = lean_unsigned_to_nat(2);
            return v___x_3990_;
        }
        3 => {
            let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
            v___x_3991_ = lean_unsigned_to_nat(3);
            return v___x_3991_;
        }
        4 => {
            let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
            v___x_3992_ = lean_unsigned_to_nat(4);
            return v___x_3992_;
        }
        5 => {
            let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
            v___x_3993_ = lean_unsigned_to_nat(5);
            return v___x_3993_;
        }
        6 => {
            let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
            v___x_3994_ = lean_unsigned_to_nat(6);
            return v___x_3994_;
        }
        7 => {
            let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
            v___x_3995_ = lean_unsigned_to_nat(7);
            return v___x_3995_;
        }
        8 => {
            let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
            v___x_3996_ = lean_unsigned_to_nat(8);
            return v___x_3996_;
        }
        9 => {
            let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
            v___x_3997_ = lean_unsigned_to_nat(9);
            return v___x_3997_;
        }
        10 => {
            let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
            v___x_3998_ = lean_unsigned_to_nat(10);
            return v___x_3998_;
        }
        11 => {
            let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
            v___x_3999_ = lean_unsigned_to_nat(11);
            return v___x_3999_;
        }
        12 => {
            let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
            v___x_4000_ = lean_unsigned_to_nat(12);
            return v___x_4000_;
        }
        _ => {
            let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
            v___x_4001_ = lean_unsigned_to_nat(13);
            return v___x_4001_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_ctorIdx___boxed(mut v_x_4002_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4003_: *mut LeanObject = core::ptr::null_mut();
    v_res_4003_ = l_Lean_IR_IRType_ctorIdx(v_x_4002_);
    lean_dec(v_x_4002_);
    return v_res_4003_;
}
pub unsafe fn l_Lean_IR_IRType_ctorElim___redArg(
    mut v_t_4004_: *mut LeanObject,
    mut v_k_4005_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4004_) {
        10 => {
            let mut v_leanTypeName_4006_: *mut LeanObject = core::ptr::null_mut();
            let mut v_types_4007_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
            v_leanTypeName_4006_ = lean_ctor_get(v_t_4004_, 0);
            lean_inc(v_leanTypeName_4006_);
            v_types_4007_ = lean_ctor_get(v_t_4004_, 1);
            lean_inc_ref(v_types_4007_);
            lean_dec_ref_known(v_t_4004_, 2);
            v___x_4008_ = lean_apply_2(v_k_4005_, v_leanTypeName_4006_, v_types_4007_);
            return v___x_4008_;
        }
        11 => {
            let mut v_leanTypeName_4009_: *mut LeanObject = core::ptr::null_mut();
            let mut v_types_4010_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
            v_leanTypeName_4009_ = lean_ctor_get(v_t_4004_, 0);
            lean_inc(v_leanTypeName_4009_);
            v_types_4010_ = lean_ctor_get(v_t_4004_, 1);
            lean_inc_ref(v_types_4010_);
            lean_dec_ref_known(v_t_4004_, 2);
            v___x_4011_ = lean_apply_2(v_k_4005_, v_leanTypeName_4009_, v_types_4010_);
            return v___x_4011_;
        }
        _ => {
            lean_dec(v_t_4004_);
            return v_k_4005_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_ctorElim(
    mut v_motive__1_4012_: *mut LeanObject,
    mut v_ctorIdx_4013_: *mut LeanObject,
    mut v_t_4014_: *mut LeanObject,
    mut v_h_4015_: *mut LeanObject,
    mut v_k_4016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    v___x_4017_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4014_, v_k_4016_);
    return v___x_4017_;
}
pub unsafe fn l_Lean_IR_IRType_ctorElim___boxed(
    mut v_motive__1_4018_: *mut LeanObject,
    mut v_ctorIdx_4019_: *mut LeanObject,
    mut v_t_4020_: *mut LeanObject,
    mut v_h_4021_: *mut LeanObject,
    mut v_k_4022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4023_: *mut LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_IR_IRType_ctorElim(
        v_motive__1_4018_,
        v_ctorIdx_4019_,
        v_t_4020_,
        v_h_4021_,
        v_k_4022_,
    );
    lean_dec(v_ctorIdx_4019_);
    return v_res_4023_;
}
pub unsafe fn l_Lean_IR_IRType_float_elim___redArg(
    mut v_t_4024_: *mut LeanObject,
    mut v_float_4025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    v___x_4026_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4024_, v_float_4025_);
    return v___x_4026_;
}
pub unsafe fn l_Lean_IR_IRType_float_elim(
    mut v_motive__1_4027_: *mut LeanObject,
    mut v_t_4028_: *mut LeanObject,
    mut v_h_4029_: *mut LeanObject,
    mut v_float_4030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    v___x_4031_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4028_, v_float_4030_);
    return v___x_4031_;
}
pub unsafe fn l_Lean_IR_IRType_uint8_elim___redArg(
    mut v_t_4032_: *mut LeanObject,
    mut v_uint8_4033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    v___x_4034_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4032_, v_uint8_4033_);
    return v___x_4034_;
}
pub unsafe fn l_Lean_IR_IRType_uint8_elim(
    mut v_motive__1_4035_: *mut LeanObject,
    mut v_t_4036_: *mut LeanObject,
    mut v_h_4037_: *mut LeanObject,
    mut v_uint8_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    v___x_4039_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4036_, v_uint8_4038_);
    return v___x_4039_;
}
pub unsafe fn l_Lean_IR_IRType_uint16_elim___redArg(
    mut v_t_4040_: *mut LeanObject,
    mut v_uint16_4041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    v___x_4042_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4040_, v_uint16_4041_);
    return v___x_4042_;
}
pub unsafe fn l_Lean_IR_IRType_uint16_elim(
    mut v_motive__1_4043_: *mut LeanObject,
    mut v_t_4044_: *mut LeanObject,
    mut v_h_4045_: *mut LeanObject,
    mut v_uint16_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    v___x_4047_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4044_, v_uint16_4046_);
    return v___x_4047_;
}
pub unsafe fn l_Lean_IR_IRType_uint32_elim___redArg(
    mut v_t_4048_: *mut LeanObject,
    mut v_uint32_4049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4048_, v_uint32_4049_);
    return v___x_4050_;
}
pub unsafe fn l_Lean_IR_IRType_uint32_elim(
    mut v_motive__1_4051_: *mut LeanObject,
    mut v_t_4052_: *mut LeanObject,
    mut v_h_4053_: *mut LeanObject,
    mut v_uint32_4054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    v___x_4055_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4052_, v_uint32_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_IR_IRType_uint64_elim___redArg(
    mut v_t_4056_: *mut LeanObject,
    mut v_uint64_4057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    v___x_4058_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4056_, v_uint64_4057_);
    return v___x_4058_;
}
pub unsafe fn l_Lean_IR_IRType_uint64_elim(
    mut v_motive__1_4059_: *mut LeanObject,
    mut v_t_4060_: *mut LeanObject,
    mut v_h_4061_: *mut LeanObject,
    mut v_uint64_4062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4060_, v_uint64_4062_);
    return v___x_4063_;
}
pub unsafe fn l_Lean_IR_IRType_usize_elim___redArg(
    mut v_t_4064_: *mut LeanObject,
    mut v_usize_4065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4064_, v_usize_4065_);
    return v___x_4066_;
}
pub unsafe fn l_Lean_IR_IRType_usize_elim(
    mut v_motive__1_4067_: *mut LeanObject,
    mut v_t_4068_: *mut LeanObject,
    mut v_h_4069_: *mut LeanObject,
    mut v_usize_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4068_, v_usize_4070_);
    return v___x_4071_;
}
pub unsafe fn l_Lean_IR_IRType_erased_elim___redArg(
    mut v_t_4072_: *mut LeanObject,
    mut v_erased_4073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    v___x_4074_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4072_, v_erased_4073_);
    return v___x_4074_;
}
pub unsafe fn l_Lean_IR_IRType_erased_elim(
    mut v_motive__1_4075_: *mut LeanObject,
    mut v_t_4076_: *mut LeanObject,
    mut v_h_4077_: *mut LeanObject,
    mut v_erased_4078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    v___x_4079_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4076_, v_erased_4078_);
    return v___x_4079_;
}
pub unsafe fn l_Lean_IR_IRType_object_elim___redArg(
    mut v_t_4080_: *mut LeanObject,
    mut v_object_4081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    v___x_4082_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4080_, v_object_4081_);
    return v___x_4082_;
}
pub unsafe fn l_Lean_IR_IRType_object_elim(
    mut v_motive__1_4083_: *mut LeanObject,
    mut v_t_4084_: *mut LeanObject,
    mut v_h_4085_: *mut LeanObject,
    mut v_object_4086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    v___x_4087_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4084_, v_object_4086_);
    return v___x_4087_;
}
pub unsafe fn l_Lean_IR_IRType_tobject_elim___redArg(
    mut v_t_4088_: *mut LeanObject,
    mut v_tobject_4089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    v___x_4090_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4088_, v_tobject_4089_);
    return v___x_4090_;
}
pub unsafe fn l_Lean_IR_IRType_tobject_elim(
    mut v_motive__1_4091_: *mut LeanObject,
    mut v_t_4092_: *mut LeanObject,
    mut v_h_4093_: *mut LeanObject,
    mut v_tobject_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4092_, v_tobject_4094_);
    return v___x_4095_;
}
pub unsafe fn l_Lean_IR_IRType_float32_elim___redArg(
    mut v_t_4096_: *mut LeanObject,
    mut v_float32_4097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4096_, v_float32_4097_);
    return v___x_4098_;
}
pub unsafe fn l_Lean_IR_IRType_float32_elim(
    mut v_motive__1_4099_: *mut LeanObject,
    mut v_t_4100_: *mut LeanObject,
    mut v_h_4101_: *mut LeanObject,
    mut v_float32_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    v___x_4103_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4100_, v_float32_4102_);
    return v___x_4103_;
}
pub unsafe fn l_Lean_IR_IRType_struct_elim___redArg(
    mut v_t_4104_: *mut LeanObject,
    mut v_struct_4105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    v___x_4106_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4104_, v_struct_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Lean_IR_IRType_struct_elim(
    mut v_motive__1_4107_: *mut LeanObject,
    mut v_t_4108_: *mut LeanObject,
    mut v_h_4109_: *mut LeanObject,
    mut v_struct_4110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    v___x_4111_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4108_, v_struct_4110_);
    return v___x_4111_;
}
pub unsafe fn l_Lean_IR_IRType_union_elim___redArg(
    mut v_t_4112_: *mut LeanObject,
    mut v_union_4113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    v___x_4114_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4112_, v_union_4113_);
    return v___x_4114_;
}
pub unsafe fn l_Lean_IR_IRType_union_elim(
    mut v_motive__1_4115_: *mut LeanObject,
    mut v_t_4116_: *mut LeanObject,
    mut v_h_4117_: *mut LeanObject,
    mut v_union_4118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4116_, v_union_4118_);
    return v___x_4119_;
}
pub unsafe fn l_Lean_IR_IRType_tagged_elim___redArg(
    mut v_t_4120_: *mut LeanObject,
    mut v_tagged_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    v___x_4122_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4120_, v_tagged_4121_);
    return v___x_4122_;
}
pub unsafe fn l_Lean_IR_IRType_tagged_elim(
    mut v_motive__1_4123_: *mut LeanObject,
    mut v_t_4124_: *mut LeanObject,
    mut v_h_4125_: *mut LeanObject,
    mut v_tagged_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4124_, v_tagged_4126_);
    return v___x_4127_;
}
pub unsafe fn l_Lean_IR_IRType_void_elim___redArg(
    mut v_t_4128_: *mut LeanObject,
    mut v_void_4129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    v___x_4130_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4128_, v_void_4129_);
    return v___x_4130_;
}
pub unsafe fn l_Lean_IR_IRType_void_elim(
    mut v_motive__1_4131_: *mut LeanObject,
    mut v_t_4132_: *mut LeanObject,
    mut v_h_4133_: *mut LeanObject,
    mut v_void_4134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    v___x_4135_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4132_, v_void_4134_);
    return v___x_4135_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedIRType_default() -> *mut LeanObject {
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    v___x_4136_ = lean_box(0);
    return v___x_4136_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedIRType() -> *mut LeanObject {
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    v___x_4137_ = lean_box(0);
    return v___x_4137_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(
    mut v_x_4138_: *mut LeanObject,
    mut v_x_4139_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4138_) == 0 {
        if lean_obj_tag(v_x_4139_) == 0 {
            let mut v___x_4140_: u8 = 0;
            v___x_4140_ = 1;
            return v___x_4140_;
        } else {
            let mut v___x_4141_: u8 = 0;
            v___x_4141_ = 0;
            return v___x_4141_;
        }
    } else {
        if lean_obj_tag(v_x_4139_) == 0 {
            let mut v___x_4142_: u8 = 0;
            v___x_4142_ = 0;
            return v___x_4142_;
        } else {
            let mut v_val_4143_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_4144_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4145_: u8 = 0;
            v_val_4143_ = lean_ctor_get(v_x_4138_, 0);
            v_val_4144_ = lean_ctor_get(v_x_4139_, 0);
            v___x_4145_ = lean_name_eq(v_val_4143_, v_val_4144_);
            return v___x_4145_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0___boxed(
    mut v_x_4146_: *mut LeanObject,
    mut v_x_4147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4148_: u8 = 0;
    let mut v_r_4149_: *mut LeanObject = core::ptr::null_mut();
    v_res_4148_ =
        l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(v_x_4146_, v_x_4147_);
    lean_dec(v_x_4147_);
    lean_dec(v_x_4146_);
    v_r_4149_ = lean_box((v_res_4148_) as usize);
    return v_r_4149_;
}
pub unsafe fn l_Lean_IR_instBEqIRType_beq(
    mut v_x_4150_: *mut LeanObject,
    mut v_x_4151_: *mut LeanObject,
) -> u8 {
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    v___x_4152_ = l_Lean_IR_IRType_ctorIdx(v_x_4150_);
    v___x_4153_ = l_Lean_IR_IRType_ctorIdx(v_x_4151_);
    v___x_4154_ = lean_nat_dec_eq(v___x_4152_, v___x_4153_);
    lean_dec(v___x_4153_);
    lean_dec(v___x_4152_);
    if v___x_4154_ == 0 {
        return v___x_4154_;
    } else {
        match lean_obj_tag(v_x_4150_) {
            10 => {
                let mut v_leanTypeName_4155_: *mut LeanObject = core::ptr::null_mut();
                let mut v_types_4156_: *mut LeanObject = core::ptr::null_mut();
                let mut v_leanTypeName_4157_: *mut LeanObject = core::ptr::null_mut();
                let mut v_types_4158_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4159_: u8 = 0;
                v_leanTypeName_4155_ = lean_ctor_get(v_x_4150_, 0);
                v_types_4156_ = lean_ctor_get(v_x_4150_, 1);
                v_leanTypeName_4157_ = lean_ctor_get(v_x_4151_, 0);
                v_types_4158_ = lean_ctor_get(v_x_4151_, 1);
                v___x_4159_ = l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(
                    v_leanTypeName_4155_,
                    v_leanTypeName_4157_,
                );
                if v___x_4159_ == 0 {
                    return v___x_4159_;
                } else {
                    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4162_: u8 = 0;
                    v___x_4160_ = lean_array_get_size(v_types_4156_);
                    v___x_4161_ = lean_array_get_size(v_types_4158_);
                    v___x_4162_ = lean_nat_dec_eq(v___x_4160_, v___x_4161_);
                    if v___x_4162_ == 0 {
                        return v___x_4162_;
                    } else {
                        let mut v___x_4163_: u8 = 0;
                        v___x_4163_ =
                            l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(
                                v_types_4156_,
                                v_types_4158_,
                                v___x_4160_,
                            );
                        return v___x_4163_;
                    }
                }
            }
            11 => {
                let mut v_leanTypeName_4164_: *mut LeanObject = core::ptr::null_mut();
                let mut v_types_4165_: *mut LeanObject = core::ptr::null_mut();
                let mut v_leanTypeName_4166_: *mut LeanObject = core::ptr::null_mut();
                let mut v_types_4167_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4168_: u8 = 0;
                v_leanTypeName_4164_ = lean_ctor_get(v_x_4150_, 0);
                v_types_4165_ = lean_ctor_get(v_x_4150_, 1);
                v_leanTypeName_4166_ = lean_ctor_get(v_x_4151_, 0);
                v_types_4167_ = lean_ctor_get(v_x_4151_, 1);
                v___x_4168_ = lean_name_eq(v_leanTypeName_4164_, v_leanTypeName_4166_);
                if v___x_4168_ == 0 {
                    return v___x_4168_;
                } else {
                    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4171_: u8 = 0;
                    v___x_4169_ = lean_array_get_size(v_types_4165_);
                    v___x_4170_ = lean_array_get_size(v_types_4167_);
                    v___x_4171_ = lean_nat_dec_eq(v___x_4169_, v___x_4170_);
                    if v___x_4171_ == 0 {
                        return v___x_4171_;
                    } else {
                        let mut v___x_4172_: u8 = 0;
                        v___x_4172_ =
                            l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(
                                v_types_4165_,
                                v_types_4167_,
                                v___x_4169_,
                            );
                        return v___x_4172_;
                    }
                }
            }
            _ => {
                return v___x_4154_;
            }
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(
    mut v_xs_4173_: *mut LeanObject,
    mut v_ys_4174_: *mut LeanObject,
    mut v_x_4175_: *mut LeanObject,
) -> u8 {
    let mut v_zero_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4177_: u8 = 0;
    let mut v_one_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4176_ = lean_unsigned_to_nat(0);
                v_isZero_4177_ = lean_nat_dec_eq(v_x_4175_, v_zero_4176_);
                if v_isZero_4177_ == 1 {
                    lean_dec(v_x_4175_);
                    return v_isZero_4177_;
                } else {
                    v_one_4178_ = lean_unsigned_to_nat(1);
                    v_n_4179_ = lean_nat_sub(v_x_4175_, v_one_4178_);
                    lean_dec(v_x_4175_);
                    v___x_4180_ = lean_array_fget_borrowed(v_xs_4173_, v_n_4179_);
                    v___x_4181_ = lean_array_fget_borrowed(v_ys_4174_, v_n_4179_);
                    v___x_4182_ = l_Lean_IR_instBEqIRType_beq(v___x_4180_, v___x_4181_);
                    if v___x_4182_ == 0 {
                        lean_dec(v_n_4179_);
                        return v___x_4182_;
                    } else {
                        v_x_4175_ = v_n_4179_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg___boxed(
    mut v_xs_4184_: *mut LeanObject,
    mut v_ys_4185_: *mut LeanObject,
    mut v_x_4186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4187_: u8 = 0;
    let mut v_r_4188_: *mut LeanObject = core::ptr::null_mut();
    v_res_4187_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(
        v_xs_4184_, v_ys_4185_, v_x_4186_,
    );
    lean_dec_ref(v_ys_4185_);
    lean_dec_ref(v_xs_4184_);
    v_r_4188_ = lean_box((v_res_4187_) as usize);
    return v_r_4188_;
}
pub unsafe fn l_Lean_IR_instBEqIRType_beq___boxed(
    mut v_x_4189_: *mut LeanObject,
    mut v_x_4190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4191_: u8 = 0;
    let mut v_r_4192_: *mut LeanObject = core::ptr::null_mut();
    v_res_4191_ = l_Lean_IR_instBEqIRType_beq(v_x_4189_, v_x_4190_);
    lean_dec(v_x_4190_);
    lean_dec(v_x_4189_);
    v_r_4192_ = lean_box((v_res_4191_) as usize);
    return v_r_4192_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(
    mut v_xs_4193_: *mut LeanObject,
    mut v_ys_4194_: *mut LeanObject,
    mut v_hsz_4195_: *mut LeanObject,
    mut v_x_4196_: *mut LeanObject,
    mut v_x_4197_: *mut LeanObject,
) -> u8 {
    let mut v___x_4198_: u8 = 0;
    v___x_4198_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(
        v_xs_4193_, v_ys_4194_, v_x_4196_,
    );
    return v___x_4198_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___boxed(
    mut v_xs_4199_: *mut LeanObject,
    mut v_ys_4200_: *mut LeanObject,
    mut v_hsz_4201_: *mut LeanObject,
    mut v_x_4202_: *mut LeanObject,
    mut v_x_4203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4204_: u8 = 0;
    let mut v_r_4205_: *mut LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(
        v_xs_4199_,
        v_ys_4200_,
        v_hsz_4201_,
        v_x_4202_,
        v_x_4203_,
    );
    lean_dec_ref(v_ys_4200_);
    lean_dec_ref(v_xs_4199_);
    v_r_4205_ = lean_box((v_res_4204_) as usize);
    return v_r_4205_;
}
pub unsafe fn l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(
    mut v_x_4214_: *mut LeanObject,
    mut v_x_4215_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4214_) == 0 {
        let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
        v___x_4216_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1;
        return v___x_4216_;
    } else {
        let mut v_val_4217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
        v_val_4217_ = lean_ctor_get(v_x_4214_, 0);
        lean_inc(v_val_4217_);
        lean_dec_ref_known(v_x_4214_, 1);
        v___x_4218_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3;
        v___x_4219_ = lean_unsigned_to_nat(1024);
        v___x_4220_ = l_Lean_Name_reprPrec(v_val_4217_, v___x_4219_);
        v___x_4221_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4221_, 0, v___x_4218_);
        lean_ctor_set(v___x_4221_, 1, v___x_4220_);
        v___x_4222_ = l_Repr_addAppParen(v___x_4221_, v_x_4215_);
        return v___x_4222_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___boxed(
    mut v_x_4223_: *mut LeanObject,
    mut v_x_4224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4225_: *mut LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(v_x_4223_, v_x_4224_);
    lean_dec(v_x_4224_);
    return v_res_4225_;
}
pub unsafe fn _init_l_Lean_IR_instReprIRType_repr___closed__24() -> *mut LeanObject {
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    v___x_4262_ = lean_unsigned_to_nat(2);
    v___x_4263_ = lean_nat_to_int(v___x_4262_);
    return v___x_4263_;
}
pub unsafe fn _init_l_Lean_IR_instReprIRType_repr___closed__25() -> *mut LeanObject {
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    v___x_4264_ = lean_unsigned_to_nat(1);
    v___x_4265_ = lean_nat_to_int(v___x_4264_);
    return v___x_4265_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(
    mut v_x_4278_: *mut LeanObject,
    mut v_x_4279_: *mut LeanObject,
    mut v_x_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4285_: u8 = 0;
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4280_) == 0 {
                    lean_dec(v_x_4278_);
                    return v_x_4279_;
                } else {
                    v_head_4281_ = lean_ctor_get(v_x_4280_, 0);
                    v_tail_4282_ = lean_ctor_get(v_x_4280_, 1);
                    v_isSharedCheck_4293_ = (!lean_is_exclusive(v_x_4280_)) as u8;
                    if v_isSharedCheck_4293_ == 0 {
                        v___x_4284_ = v_x_4280_;
                        v_isShared_4285_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4282_);
                        lean_inc(v_head_4281_);
                        lean_dec(v_x_4280_);
                        v___x_4284_ = lean_box(0);
                        v_isShared_4285_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4278_);
                if v_isShared_4285_ == 0 {
                    lean_ctor_set_tag(v___x_4284_, 5);
                    lean_ctor_set(v___x_4284_, 1, v_x_4278_);
                    lean_ctor_set(v___x_4284_, 0, v_x_4279_);
                    v___x_4287_ = v___x_4284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4292_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_x_4279_);
                    lean_ctor_set(v_reuseFailAlloc_4292_, 1, v_x_4278_);
                    v___x_4287_ = v_reuseFailAlloc_4292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4288_ = lean_unsigned_to_nat(0);
                v___x_4289_ = l_Lean_IR_instReprIRType_repr(v_head_4281_, v___x_4288_);
                v___x_4290_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4290_, 0, v___x_4287_);
                lean_ctor_set(v___x_4290_, 1, v___x_4289_);
                v_x_4279_ = v___x_4290_;
                v_x_4280_ = v_tail_4282_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(
    mut v_x_4294_: *mut LeanObject,
    mut v_x_4295_: *mut LeanObject,
    mut v_x_4296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4296_) == 0 {
                    lean_dec(v_x_4294_);
                    return v_x_4295_;
                } else {
                    v_head_4297_ = lean_ctor_get(v_x_4296_, 0);
                    v_tail_4298_ = lean_ctor_get(v_x_4296_, 1);
                    v_isSharedCheck_4309_ = (!lean_is_exclusive(v_x_4296_)) as u8;
                    if v_isSharedCheck_4309_ == 0 {
                        v___x_4300_ = v_x_4296_;
                        v_isShared_4301_ = v_isSharedCheck_4309_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4298_);
                        lean_inc(v_head_4297_);
                        lean_dec(v_x_4296_);
                        v___x_4300_ = lean_box(0);
                        v_isShared_4301_ = v_isSharedCheck_4309_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_4294_);
                if v_isShared_4301_ == 0 {
                    lean_ctor_set_tag(v___x_4300_, 5);
                    lean_ctor_set(v___x_4300_, 1, v_x_4294_);
                    lean_ctor_set(v___x_4300_, 0, v_x_4295_);
                    v___x_4303_ = v___x_4300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_x_4295_);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_x_4294_);
                    v___x_4303_ = v_reuseFailAlloc_4308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4304_ = lean_unsigned_to_nat(0);
                v___x_4305_ = l_Lean_IR_instReprIRType_repr(v_head_4297_, v___x_4304_);
                v___x_4306_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4306_, 0, v___x_4303_);
                lean_ctor_set(v___x_4306_, 1, v___x_4305_);
                v___x_4307_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(v_x_4294_, v___x_4306_, v_tail_4298_);
                return v___x_4307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(
    mut v_x_4310_: *mut LeanObject,
    mut v_x_4311_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4310_) == 0 {
        let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4311_);
        v___x_4312_ = lean_box(0);
        return v___x_4312_;
    } else {
        let mut v_tail_4313_: *mut LeanObject = core::ptr::null_mut();
        v_tail_4313_ = lean_ctor_get(v_x_4310_, 1);
        if lean_obj_tag(v_tail_4313_) == 0 {
            let mut v_head_4314_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_4311_);
            v_head_4314_ = lean_ctor_get(v_x_4310_, 0);
            lean_inc(v_head_4314_);
            lean_dec_ref_known(v_x_4310_, 2);
            v___x_4315_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_4314_);
            return v___x_4315_;
        } else {
            let mut v_head_4316_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_4313_);
            v_head_4316_ = lean_ctor_get(v_x_4310_, 0);
            lean_inc(v_head_4316_);
            lean_dec_ref_known(v_x_4310_, 2);
            v___x_4317_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_4316_);
            v___x_4318_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(v_x_4311_, v___x_4317_, v_tail_4313_);
            return v___x_4318_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    v___x_4320_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0;
    v___x_4321_ = lean_string_length(v___x_4320_);
    return v___x_4321_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6()
-> *mut LeanObject {
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    v___x_4322_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5_once
        ),
        _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5,
    );
    v___x_4323_ = lean_nat_to_int(v___x_4322_);
    return v___x_4323_;
}
pub unsafe fn l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(
    mut v_xs_4332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    v___x_4333_ = lean_array_get_size(v_xs_4332_);
    v___x_4334_ = lean_unsigned_to_nat(0);
    v___x_4335_ = lean_nat_dec_eq(v___x_4333_, v___x_4334_);
    if v___x_4335_ == 0 {
        let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
        v___x_4336_ = lean_array_to_list(v_xs_4332_);
        v___x_4337_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3;
        v___x_4338_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(v___x_4336_, v___x_4337_);
        v___x_4339_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6,
        );
        v___x_4340_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7;
        v___x_4341_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4341_, 0, v___x_4340_);
        lean_ctor_set(v___x_4341_, 1, v___x_4338_);
        v___x_4342_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8;
        v___x_4343_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_4343_, 0, v___x_4341_);
        lean_ctor_set(v___x_4343_, 1, v___x_4342_);
        v___x_4344_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_4344_, 0, v___x_4339_);
        lean_ctor_set(v___x_4344_, 1, v___x_4343_);
        v___x_4345_ = l_Std_Format_fill(v___x_4344_);
        return v___x_4345_;
    } else {
        let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_4332_);
        v___x_4346_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10;
        return v___x_4346_;
    }
}
pub unsafe fn l_Lean_IR_instReprIRType_repr(
    mut v_x_4353_: *mut LeanObject,
    mut v_prec_4354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: u8 = 0;
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: u8 = 0;
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: u8 = 0;
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: u8 = 0;
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: u8 = 0;
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: u8 = 0;
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: u8 = 0;
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: u8 = 0;
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: u8 = 0;
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: u8 = 0;
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: u8 = 0;
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leanTypeName_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_types_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v___y_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_leanTypeName_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_types_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___y_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: u8 = 0;
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: u8 = 0;
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: u8 = 0;
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4353_) {
                0 => {
                    v___x_4439_ = lean_unsigned_to_nat(1024);
                    v___x_4440_ = lean_nat_dec_le(v___x_4439_, v_prec_4354_);
                    if v___x_4440_ == 0 {
                        v___x_4441_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4356_ = v___x_4441_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4442_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4356_ = v___x_4442_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4443_ = lean_unsigned_to_nat(1024);
                    v___x_4444_ = lean_nat_dec_le(v___x_4443_, v_prec_4354_);
                    if v___x_4444_ == 0 {
                        v___x_4445_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4363_ = v___x_4445_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4446_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4363_ = v___x_4446_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_4447_ = lean_unsigned_to_nat(1024);
                    v___x_4448_ = lean_nat_dec_le(v___x_4447_, v_prec_4354_);
                    if v___x_4448_ == 0 {
                        v___x_4449_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4370_ = v___x_4449_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4450_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4370_ = v___x_4450_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_4451_ = lean_unsigned_to_nat(1024);
                    v___x_4452_ = lean_nat_dec_le(v___x_4451_, v_prec_4354_);
                    if v___x_4452_ == 0 {
                        v___x_4453_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4377_ = v___x_4453_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4454_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4377_ = v___x_4454_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v___x_4455_ = lean_unsigned_to_nat(1024);
                    v___x_4456_ = lean_nat_dec_le(v___x_4455_, v_prec_4354_);
                    if v___x_4456_ == 0 {
                        v___x_4457_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4384_ = v___x_4457_;
                        state = 5;
                        continue;
                    } else {
                        v___x_4458_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4384_ = v___x_4458_;
                        state = 5;
                        continue;
                    }
                }
                5 => {
                    v___x_4459_ = lean_unsigned_to_nat(1024);
                    v___x_4460_ = lean_nat_dec_le(v___x_4459_, v_prec_4354_);
                    if v___x_4460_ == 0 {
                        v___x_4461_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4391_ = v___x_4461_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4462_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4391_ = v___x_4462_;
                        state = 6;
                        continue;
                    }
                }
                6 => {
                    v___x_4463_ = lean_unsigned_to_nat(1024);
                    v___x_4464_ = lean_nat_dec_le(v___x_4463_, v_prec_4354_);
                    if v___x_4464_ == 0 {
                        v___x_4465_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4398_ = v___x_4465_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4466_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4398_ = v___x_4466_;
                        state = 7;
                        continue;
                    }
                }
                7 => {
                    v___x_4467_ = lean_unsigned_to_nat(1024);
                    v___x_4468_ = lean_nat_dec_le(v___x_4467_, v_prec_4354_);
                    if v___x_4468_ == 0 {
                        v___x_4469_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4405_ = v___x_4469_;
                        state = 8;
                        continue;
                    } else {
                        v___x_4470_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4405_ = v___x_4470_;
                        state = 8;
                        continue;
                    }
                }
                8 => {
                    v___x_4471_ = lean_unsigned_to_nat(1024);
                    v___x_4472_ = lean_nat_dec_le(v___x_4471_, v_prec_4354_);
                    if v___x_4472_ == 0 {
                        v___x_4473_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4412_ = v___x_4473_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4474_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4412_ = v___x_4474_;
                        state = 9;
                        continue;
                    }
                }
                9 => {
                    v___x_4475_ = lean_unsigned_to_nat(1024);
                    v___x_4476_ = lean_nat_dec_le(v___x_4475_, v_prec_4354_);
                    if v___x_4476_ == 0 {
                        v___x_4477_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4419_ = v___x_4477_;
                        state = 10;
                        continue;
                    } else {
                        v___x_4478_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4419_ = v___x_4478_;
                        state = 10;
                        continue;
                    }
                }
                10 => {
                    v_leanTypeName_4479_ = lean_ctor_get(v_x_4353_, 0);
                    v_types_4480_ = lean_ctor_get(v_x_4353_, 1);
                    v_isSharedCheck_4504_ = (!lean_is_exclusive(v_x_4353_)) as u8;
                    if v_isSharedCheck_4504_ == 0 {
                        v___x_4482_ = v_x_4353_;
                        v_isShared_4483_ = v_isSharedCheck_4504_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_types_4480_);
                        lean_inc(v_leanTypeName_4479_);
                        lean_dec(v_x_4353_);
                        v___x_4482_ = lean_box(0);
                        v_isShared_4483_ = v_isSharedCheck_4504_;
                        state = 13;
                        continue;
                    }
                }
                11 => {
                    v_leanTypeName_4505_ = lean_ctor_get(v_x_4353_, 0);
                    v_types_4506_ = lean_ctor_get(v_x_4353_, 1);
                    v_isSharedCheck_4530_ = (!lean_is_exclusive(v_x_4353_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4508_ = v_x_4353_;
                        v_isShared_4509_ = v_isSharedCheck_4530_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_types_4506_);
                        lean_inc(v_leanTypeName_4505_);
                        lean_dec(v_x_4353_);
                        v___x_4508_ = lean_box(0);
                        v_isShared_4509_ = v_isSharedCheck_4530_;
                        state = 16;
                        continue;
                    }
                }
                12 => {
                    v___x_4531_ = lean_unsigned_to_nat(1024);
                    v___x_4532_ = lean_nat_dec_le(v___x_4531_, v_prec_4354_);
                    if v___x_4532_ == 0 {
                        v___x_4533_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4426_ = v___x_4533_;
                        state = 11;
                        continue;
                    } else {
                        v___x_4534_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4426_ = v___x_4534_;
                        state = 11;
                        continue;
                    }
                }
                _ => {
                    v___x_4535_ = lean_unsigned_to_nat(1024);
                    v___x_4536_ = lean_nat_dec_le(v___x_4535_, v_prec_4354_);
                    if v___x_4536_ == 0 {
                        v___x_4537_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4433_ = v___x_4537_;
                        state = 12;
                        continue;
                    } else {
                        v___x_4538_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4433_ = v___x_4538_;
                        state = 12;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4357_ = l_Lean_IR_instReprIRType_repr___closed__1;
                lean_inc(v___y_4356_);
                v___x_4358_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4358_, 0, v___y_4356_);
                lean_ctor_set(v___x_4358_, 1, v___x_4357_);
                v___x_4359_ = 0;
                v___x_4360_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4360_, 0, v___x_4358_);
                lean_ctor_set_uint8(
                    v___x_4360_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4359_,
                );
                v___x_4361_ = l_Repr_addAppParen(v___x_4360_, v_prec_4354_);
                return v___x_4361_;
            }
            2 => {
                v___x_4364_ = l_Lean_IR_instReprIRType_repr___closed__3;
                lean_inc(v___y_4363_);
                v___x_4365_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4365_, 0, v___y_4363_);
                lean_ctor_set(v___x_4365_, 1, v___x_4364_);
                v___x_4366_ = 0;
                v___x_4367_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4367_, 0, v___x_4365_);
                lean_ctor_set_uint8(
                    v___x_4367_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4366_,
                );
                v___x_4368_ = l_Repr_addAppParen(v___x_4367_, v_prec_4354_);
                return v___x_4368_;
            }
            3 => {
                v___x_4371_ = l_Lean_IR_instReprIRType_repr___closed__5;
                lean_inc(v___y_4370_);
                v___x_4372_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4372_, 0, v___y_4370_);
                lean_ctor_set(v___x_4372_, 1, v___x_4371_);
                v___x_4373_ = 0;
                v___x_4374_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4374_, 0, v___x_4372_);
                lean_ctor_set_uint8(
                    v___x_4374_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4373_,
                );
                v___x_4375_ = l_Repr_addAppParen(v___x_4374_, v_prec_4354_);
                return v___x_4375_;
            }
            4 => {
                v___x_4378_ = l_Lean_IR_instReprIRType_repr___closed__7;
                lean_inc(v___y_4377_);
                v___x_4379_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4379_, 0, v___y_4377_);
                lean_ctor_set(v___x_4379_, 1, v___x_4378_);
                v___x_4380_ = 0;
                v___x_4381_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4381_, 0, v___x_4379_);
                lean_ctor_set_uint8(
                    v___x_4381_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4380_,
                );
                v___x_4382_ = l_Repr_addAppParen(v___x_4381_, v_prec_4354_);
                return v___x_4382_;
            }
            5 => {
                v___x_4385_ = l_Lean_IR_instReprIRType_repr___closed__9;
                lean_inc(v___y_4384_);
                v___x_4386_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4386_, 0, v___y_4384_);
                lean_ctor_set(v___x_4386_, 1, v___x_4385_);
                v___x_4387_ = 0;
                v___x_4388_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4388_, 0, v___x_4386_);
                lean_ctor_set_uint8(
                    v___x_4388_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4387_,
                );
                v___x_4389_ = l_Repr_addAppParen(v___x_4388_, v_prec_4354_);
                return v___x_4389_;
            }
            6 => {
                v___x_4392_ = l_Lean_IR_instReprIRType_repr___closed__11;
                lean_inc(v___y_4391_);
                v___x_4393_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4393_, 0, v___y_4391_);
                lean_ctor_set(v___x_4393_, 1, v___x_4392_);
                v___x_4394_ = 0;
                v___x_4395_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4395_, 0, v___x_4393_);
                lean_ctor_set_uint8(
                    v___x_4395_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4394_,
                );
                v___x_4396_ = l_Repr_addAppParen(v___x_4395_, v_prec_4354_);
                return v___x_4396_;
            }
            7 => {
                v___x_4399_ = l_Lean_IR_instReprIRType_repr___closed__13;
                lean_inc(v___y_4398_);
                v___x_4400_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4400_, 0, v___y_4398_);
                lean_ctor_set(v___x_4400_, 1, v___x_4399_);
                v___x_4401_ = 0;
                v___x_4402_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4402_, 0, v___x_4400_);
                lean_ctor_set_uint8(
                    v___x_4402_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4401_,
                );
                v___x_4403_ = l_Repr_addAppParen(v___x_4402_, v_prec_4354_);
                return v___x_4403_;
            }
            8 => {
                v___x_4406_ = l_Lean_IR_instReprIRType_repr___closed__15;
                lean_inc(v___y_4405_);
                v___x_4407_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4407_, 0, v___y_4405_);
                lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                v___x_4408_ = 0;
                v___x_4409_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4409_, 0, v___x_4407_);
                lean_ctor_set_uint8(
                    v___x_4409_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4408_,
                );
                v___x_4410_ = l_Repr_addAppParen(v___x_4409_, v_prec_4354_);
                return v___x_4410_;
            }
            9 => {
                v___x_4413_ = l_Lean_IR_instReprIRType_repr___closed__17;
                lean_inc(v___y_4412_);
                v___x_4414_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4414_, 0, v___y_4412_);
                lean_ctor_set(v___x_4414_, 1, v___x_4413_);
                v___x_4415_ = 0;
                v___x_4416_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4416_, 0, v___x_4414_);
                lean_ctor_set_uint8(
                    v___x_4416_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4415_,
                );
                v___x_4417_ = l_Repr_addAppParen(v___x_4416_, v_prec_4354_);
                return v___x_4417_;
            }
            10 => {
                v___x_4420_ = l_Lean_IR_instReprIRType_repr___closed__19;
                lean_inc(v___y_4419_);
                v___x_4421_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4421_, 0, v___y_4419_);
                lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                v___x_4422_ = 0;
                v___x_4423_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4423_, 0, v___x_4421_);
                lean_ctor_set_uint8(
                    v___x_4423_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4422_,
                );
                v___x_4424_ = l_Repr_addAppParen(v___x_4423_, v_prec_4354_);
                return v___x_4424_;
            }
            11 => {
                v___x_4427_ = l_Lean_IR_instReprIRType_repr___closed__21;
                lean_inc(v___y_4426_);
                v___x_4428_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4428_, 0, v___y_4426_);
                lean_ctor_set(v___x_4428_, 1, v___x_4427_);
                v___x_4429_ = 0;
                v___x_4430_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4430_, 0, v___x_4428_);
                lean_ctor_set_uint8(
                    v___x_4430_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4429_,
                );
                v___x_4431_ = l_Repr_addAppParen(v___x_4430_, v_prec_4354_);
                return v___x_4431_;
            }
            12 => {
                v___x_4434_ = l_Lean_IR_instReprIRType_repr___closed__23;
                lean_inc(v___y_4433_);
                v___x_4435_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4435_, 0, v___y_4433_);
                lean_ctor_set(v___x_4435_, 1, v___x_4434_);
                v___x_4436_ = 0;
                v___x_4437_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4437_, 0, v___x_4435_);
                lean_ctor_set_uint8(
                    v___x_4437_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4436_,
                );
                v___x_4438_ = l_Repr_addAppParen(v___x_4437_, v_prec_4354_);
                return v___x_4438_;
            }
            13 => {
                v___x_4500_ = lean_unsigned_to_nat(1024);
                v___x_4501_ = lean_nat_dec_le(v___x_4500_, v_prec_4354_);
                if v___x_4501_ == 0 {
                    v___x_4502_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24_once),
                        _init_l_Lean_IR_instReprIRType_repr___closed__24,
                    );
                    v___y_4485_ = v___x_4502_;
                    state = 14;
                    continue;
                } else {
                    v___x_4503_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25_once),
                        _init_l_Lean_IR_instReprIRType_repr___closed__25,
                    );
                    v___y_4485_ = v___x_4503_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4486_ = lean_box(1);
                v___x_4487_ = l_Lean_IR_instReprIRType_repr___closed__28;
                v___x_4488_ = lean_unsigned_to_nat(1024);
                v___x_4489_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(
                    v_leanTypeName_4479_,
                    v___x_4488_,
                );
                if v_isShared_4483_ == 0 {
                    lean_ctor_set_tag(v___x_4482_, 5);
                    lean_ctor_set(v___x_4482_, 1, v___x_4489_);
                    lean_ctor_set(v___x_4482_, 0, v___x_4487_);
                    v___x_4491_ = v___x_4482_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4499_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4487_);
                    lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4489_);
                    v___x_4491_ = v_reuseFailAlloc_4499_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4492_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4492_, 0, v___x_4491_);
                lean_ctor_set(v___x_4492_, 1, v___x_4486_);
                v___x_4493_ =
                    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_4480_);
                v___x_4494_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4494_, 0, v___x_4492_);
                lean_ctor_set(v___x_4494_, 1, v___x_4493_);
                lean_inc(v___y_4485_);
                v___x_4495_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4495_, 0, v___y_4485_);
                lean_ctor_set(v___x_4495_, 1, v___x_4494_);
                v___x_4496_ = 0;
                v___x_4497_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4497_, 0, v___x_4495_);
                lean_ctor_set_uint8(
                    v___x_4497_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4496_,
                );
                v___x_4498_ = l_Repr_addAppParen(v___x_4497_, v_prec_4354_);
                return v___x_4498_;
            }
            16 => {
                v___x_4526_ = lean_unsigned_to_nat(1024);
                v___x_4527_ = lean_nat_dec_le(v___x_4526_, v_prec_4354_);
                if v___x_4527_ == 0 {
                    v___x_4528_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24_once),
                        _init_l_Lean_IR_instReprIRType_repr___closed__24,
                    );
                    v___y_4511_ = v___x_4528_;
                    state = 17;
                    continue;
                } else {
                    v___x_4529_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25_once),
                        _init_l_Lean_IR_instReprIRType_repr___closed__25,
                    );
                    v___y_4511_ = v___x_4529_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4512_ = lean_box(1);
                v___x_4513_ = l_Lean_IR_instReprIRType_repr___closed__31;
                v___x_4514_ = lean_unsigned_to_nat(1024);
                v___x_4515_ = l_Lean_Name_reprPrec(v_leanTypeName_4505_, v___x_4514_);
                if v_isShared_4509_ == 0 {
                    lean_ctor_set_tag(v___x_4508_, 5);
                    lean_ctor_set(v___x_4508_, 1, v___x_4515_);
                    lean_ctor_set(v___x_4508_, 0, v___x_4513_);
                    v___x_4517_ = v___x_4508_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4513_);
                    lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___x_4515_);
                    v___x_4517_ = v_reuseFailAlloc_4525_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4518_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4518_, 0, v___x_4517_);
                lean_ctor_set(v___x_4518_, 1, v___x_4512_);
                v___x_4519_ =
                    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_4506_);
                v___x_4520_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4520_, 0, v___x_4518_);
                lean_ctor_set(v___x_4520_, 1, v___x_4519_);
                lean_inc(v___y_4511_);
                v___x_4521_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4521_, 0, v___y_4511_);
                lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                v___x_4522_ = 0;
                v___x_4523_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4523_, 0, v___x_4521_);
                lean_ctor_set_uint8(
                    v___x_4523_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4522_,
                );
                v___x_4524_ = l_Repr_addAppParen(v___x_4523_, v_prec_4354_);
                return v___x_4524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(
    mut v___y_4539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    v___x_4540_ = lean_unsigned_to_nat(0);
    v___x_4541_ = l_Lean_IR_instReprIRType_repr(v___y_4539_, v___x_4540_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_IR_instReprIRType_repr___boxed(
    mut v_x_4542_: *mut LeanObject,
    mut v_prec_4543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4544_: *mut LeanObject = core::ptr::null_mut();
    v_res_4544_ = l_Lean_IR_instReprIRType_repr(v_x_4542_, v_prec_4543_);
    lean_dec(v_prec_4543_);
    return v_res_4544_;
}
pub unsafe fn l_Lean_IR_IRType_isScalar(mut v_x_4547_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_x_4547_) {
        0 => {
            let mut v___x_4548_: u8 = 0;
            v___x_4548_ = 1;
            return v___x_4548_;
        }
        9 => {
            let mut v___x_4549_: u8 = 0;
            v___x_4549_ = 1;
            return v___x_4549_;
        }
        1 => {
            let mut v___x_4550_: u8 = 0;
            v___x_4550_ = 1;
            return v___x_4550_;
        }
        2 => {
            let mut v___x_4551_: u8 = 0;
            v___x_4551_ = 1;
            return v___x_4551_;
        }
        3 => {
            let mut v___x_4552_: u8 = 0;
            v___x_4552_ = 1;
            return v___x_4552_;
        }
        4 => {
            let mut v___x_4553_: u8 = 0;
            v___x_4553_ = 1;
            return v___x_4553_;
        }
        5 => {
            let mut v___x_4554_: u8 = 0;
            v___x_4554_ = 1;
            return v___x_4554_;
        }
        _ => {
            let mut v___x_4555_: u8 = 0;
            v___x_4555_ = 0;
            return v___x_4555_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_isScalar___boxed(mut v_x_4556_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4557_: u8 = 0;
    let mut v_r_4558_: *mut LeanObject = core::ptr::null_mut();
    v_res_4557_ = l_Lean_IR_IRType_isScalar(v_x_4556_);
    lean_dec(v_x_4556_);
    v_r_4558_ = lean_box((v_res_4557_) as usize);
    return v_r_4558_;
}
pub unsafe fn l_Lean_IR_IRType_isObj(mut v_x_4559_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_x_4559_) {
        7 => {
            let mut v___x_4560_: u8 = 0;
            v___x_4560_ = 1;
            return v___x_4560_;
        }
        12 => {
            let mut v___x_4561_: u8 = 0;
            v___x_4561_ = 1;
            return v___x_4561_;
        }
        8 => {
            let mut v___x_4562_: u8 = 0;
            v___x_4562_ = 1;
            return v___x_4562_;
        }
        13 => {
            let mut v___x_4563_: u8 = 0;
            v___x_4563_ = 1;
            return v___x_4563_;
        }
        _ => {
            let mut v___x_4564_: u8 = 0;
            v___x_4564_ = 0;
            return v___x_4564_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_isObj___boxed(mut v_x_4565_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4566_: u8 = 0;
    let mut v_r_4567_: *mut LeanObject = core::ptr::null_mut();
    v_res_4566_ = l_Lean_IR_IRType_isObj(v_x_4565_);
    lean_dec(v_x_4565_);
    v_r_4567_ = lean_box((v_res_4566_) as usize);
    return v_r_4567_;
}
pub unsafe fn l_Lean_IR_IRType_isPossibleRef(mut v_x_4568_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_x_4568_) {
        7 => {
            let mut v___x_4569_: u8 = 0;
            v___x_4569_ = 1;
            return v___x_4569_;
        }
        8 => {
            let mut v___x_4570_: u8 = 0;
            v___x_4570_ = 1;
            return v___x_4570_;
        }
        _ => {
            let mut v___x_4571_: u8 = 0;
            v___x_4571_ = 0;
            return v___x_4571_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_isPossibleRef___boxed(
    mut v_x_4572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4573_: u8 = 0;
    let mut v_r_4574_: *mut LeanObject = core::ptr::null_mut();
    v_res_4573_ = l_Lean_IR_IRType_isPossibleRef(v_x_4572_);
    lean_dec(v_x_4572_);
    v_r_4574_ = lean_box((v_res_4573_) as usize);
    return v_r_4574_;
}
pub unsafe fn l_Lean_IR_IRType_isDefiniteRef(mut v_x_4575_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4575_) == 7 {
        let mut v___x_4576_: u8 = 0;
        v___x_4576_ = 1;
        return v___x_4576_;
    } else {
        let mut v___x_4577_: u8 = 0;
        v___x_4577_ = 0;
        return v___x_4577_;
    }
}
pub unsafe fn l_Lean_IR_IRType_isDefiniteRef___boxed(
    mut v_x_4578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4579_: u8 = 0;
    let mut v_r_4580_: *mut LeanObject = core::ptr::null_mut();
    v_res_4579_ = l_Lean_IR_IRType_isDefiniteRef(v_x_4578_);
    lean_dec(v_x_4578_);
    v_r_4580_ = lean_box((v_res_4579_) as usize);
    return v_r_4580_;
}
pub unsafe fn l_Lean_IR_IRType_isErased(mut v_x_4581_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4581_) == 6 {
        let mut v___x_4582_: u8 = 0;
        v___x_4582_ = 1;
        return v___x_4582_;
    } else {
        let mut v___x_4583_: u8 = 0;
        v___x_4583_ = 0;
        return v___x_4583_;
    }
}
pub unsafe fn l_Lean_IR_IRType_isErased___boxed(mut v_x_4584_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4585_: u8 = 0;
    let mut v_r_4586_: *mut LeanObject = core::ptr::null_mut();
    v_res_4585_ = l_Lean_IR_IRType_isErased(v_x_4584_);
    lean_dec(v_x_4584_);
    v_r_4586_ = lean_box((v_res_4585_) as usize);
    return v_r_4586_;
}
pub unsafe fn l_Lean_IR_IRType_isVoid(mut v_x_4587_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_4587_) == 13 {
        let mut v___x_4588_: u8 = 0;
        v___x_4588_ = 1;
        return v___x_4588_;
    } else {
        let mut v___x_4589_: u8 = 0;
        v___x_4589_ = 0;
        return v___x_4589_;
    }
}
pub unsafe fn l_Lean_IR_IRType_isVoid___boxed(mut v_x_4590_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4591_: u8 = 0;
    let mut v_r_4592_: *mut LeanObject = core::ptr::null_mut();
    v_res_4591_ = l_Lean_IR_IRType_isVoid(v_x_4590_);
    lean_dec(v_x_4590_);
    v_r_4592_ = lean_box((v_res_4591_) as usize);
    return v_r_4592_;
}
pub unsafe fn l_Lean_IR_IRType_boxed(mut v_x_4593_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4593_) {
        7 => {
            return v_x_4593_;
        }
        0 => {
            let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
            v___x_4594_ = lean_box(7);
            return v___x_4594_;
        }
        9 => {
            let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
            v___x_4595_ = lean_box(7);
            return v___x_4595_;
        }
        13 => {
            let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
            v___x_4596_ = lean_box(12);
            return v___x_4596_;
        }
        12 => {
            return v_x_4593_;
        }
        1 => {
            let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
            v___x_4597_ = lean_box(12);
            return v___x_4597_;
        }
        2 => {
            let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
            v___x_4598_ = lean_box(12);
            return v___x_4598_;
        }
        _ => {
            let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
            v___x_4599_ = lean_box(8);
            return v___x_4599_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_boxed___boxed(mut v_x_4600_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4601_: *mut LeanObject = core::ptr::null_mut();
    v_res_4601_ = l_Lean_IR_IRType_boxed(v_x_4600_);
    lean_dec(v_x_4600_);
    return v_res_4601_;
}
pub unsafe fn l_Lean_IR_Arg_ctorIdx(mut v_x_4602_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_4602_) == 0 {
        let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
        v___x_4603_ = lean_unsigned_to_nat(0);
        return v___x_4603_;
    } else {
        let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
        v___x_4604_ = lean_unsigned_to_nat(1);
        return v___x_4604_;
    }
}
pub unsafe fn l_Lean_IR_Arg_ctorIdx___boxed(mut v_x_4605_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4606_: *mut LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_Lean_IR_Arg_ctorIdx(v_x_4605_);
    lean_dec(v_x_4605_);
    return v_res_4606_;
}
pub unsafe fn l_Lean_IR_Arg_ctorElim___redArg(
    mut v_t_4607_: *mut LeanObject,
    mut v_k_4608_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4607_) == 0 {
        let mut v_id_4609_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
        v_id_4609_ = lean_ctor_get(v_t_4607_, 0);
        lean_inc(v_id_4609_);
        lean_dec_ref_known(v_t_4607_, 1);
        v___x_4610_ = lean_apply_1(v_k_4608_, v_id_4609_);
        return v___x_4610_;
    } else {
        return v_k_4608_;
    }
}
pub unsafe fn l_Lean_IR_Arg_ctorElim(
    mut v_motive_4611_: *mut LeanObject,
    mut v_ctorIdx_4612_: *mut LeanObject,
    mut v_t_4613_: *mut LeanObject,
    mut v_h_4614_: *mut LeanObject,
    mut v_k_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    v___x_4616_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4613_, v_k_4615_);
    return v___x_4616_;
}
pub unsafe fn l_Lean_IR_Arg_ctorElim___boxed(
    mut v_motive_4617_: *mut LeanObject,
    mut v_ctorIdx_4618_: *mut LeanObject,
    mut v_t_4619_: *mut LeanObject,
    mut v_h_4620_: *mut LeanObject,
    mut v_k_4621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4622_: *mut LeanObject = core::ptr::null_mut();
    v_res_4622_ = l_Lean_IR_Arg_ctorElim(
        v_motive_4617_,
        v_ctorIdx_4618_,
        v_t_4619_,
        v_h_4620_,
        v_k_4621_,
    );
    lean_dec(v_ctorIdx_4618_);
    return v_res_4622_;
}
pub unsafe fn l_Lean_IR_Arg_var_elim___redArg(
    mut v_t_4623_: *mut LeanObject,
    mut v_var_4624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4623_, v_var_4624_);
    return v___x_4625_;
}
pub unsafe fn l_Lean_IR_Arg_var_elim(
    mut v_motive_4626_: *mut LeanObject,
    mut v_t_4627_: *mut LeanObject,
    mut v_h_4628_: *mut LeanObject,
    mut v_var_4629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    v___x_4630_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4627_, v_var_4629_);
    return v___x_4630_;
}
pub unsafe fn l_Lean_IR_Arg_erased_elim___redArg(
    mut v_t_4631_: *mut LeanObject,
    mut v_erased_4632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    v___x_4633_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4631_, v_erased_4632_);
    return v___x_4633_;
}
pub unsafe fn l_Lean_IR_Arg_erased_elim(
    mut v_motive_4634_: *mut LeanObject,
    mut v_t_4635_: *mut LeanObject,
    mut v_h_4636_: *mut LeanObject,
    mut v_erased_4637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    v___x_4638_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4635_, v_erased_4637_);
    return v___x_4638_;
}
pub unsafe fn l_Lean_IR_instBEqArg_beq(
    mut v_x_4643_: *mut LeanObject,
    mut v_x_4644_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4643_) == 0 {
        if lean_obj_tag(v_x_4644_) == 0 {
            let mut v_id_4645_: *mut LeanObject = core::ptr::null_mut();
            let mut v_id_4646_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4647_: u8 = 0;
            v_id_4645_ = lean_ctor_get(v_x_4643_, 0);
            v_id_4646_ = lean_ctor_get(v_x_4644_, 0);
            v___x_4647_ = lean_nat_dec_eq(v_id_4645_, v_id_4646_);
            return v___x_4647_;
        } else {
            let mut v___x_4648_: u8 = 0;
            v___x_4648_ = 0;
            return v___x_4648_;
        }
    } else {
        if lean_obj_tag(v_x_4644_) == 1 {
            let mut v___x_4649_: u8 = 0;
            v___x_4649_ = 1;
            return v___x_4649_;
        } else {
            let mut v___x_4650_: u8 = 0;
            v___x_4650_ = 0;
            return v___x_4650_;
        }
    }
}
pub unsafe fn l_Lean_IR_instBEqArg_beq___boxed(
    mut v_x_4651_: *mut LeanObject,
    mut v_x_4652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4653_: u8 = 0;
    let mut v_r_4654_: *mut LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_IR_instBEqArg_beq(v_x_4651_, v_x_4652_);
    lean_dec(v_x_4652_);
    lean_dec(v_x_4651_);
    v_r_4654_ = lean_box((v_res_4653_) as usize);
    return v_r_4654_;
}
pub unsafe fn l_Lean_IR_instReprArg_repr(
    mut v_x_4666_: *mut LeanObject,
    mut v_prec_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: u8 = 0;
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: u8 = 0;
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4666_) == 0 {
                    v_id_4675_ = lean_ctor_get(v_x_4666_, 0);
                    lean_inc(v_id_4675_);
                    lean_dec_ref_known(v_x_4666_, 1);
                    v___x_4685_ = lean_unsigned_to_nat(1024);
                    v___x_4686_ = lean_nat_dec_le(v___x_4685_, v_prec_4667_);
                    if v___x_4686_ == 0 {
                        v___x_4687_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4677_ = v___x_4687_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4688_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4677_ = v___x_4688_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4689_ = lean_unsigned_to_nat(1024);
                    v___x_4690_ = lean_nat_dec_le(v___x_4689_, v_prec_4667_);
                    if v___x_4690_ == 0 {
                        v___x_4691_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__24_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__24,
                        );
                        v___y_4669_ = v___x_4691_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4692_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__25),
                            core::ptr::addr_of_mut!(
                                l_Lean_IR_instReprIRType_repr___closed__25_once
                            ),
                            _init_l_Lean_IR_instReprIRType_repr___closed__25,
                        );
                        v___y_4669_ = v___x_4692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4670_ = l_Lean_IR_instReprArg_repr___closed__1;
                lean_inc(v___y_4669_);
                v___x_4671_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4671_, 0, v___y_4669_);
                lean_ctor_set(v___x_4671_, 1, v___x_4670_);
                v___x_4672_ = 0;
                v___x_4673_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4673_, 0, v___x_4671_);
                lean_ctor_set_uint8(
                    v___x_4673_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4672_,
                );
                v___x_4674_ = l_Repr_addAppParen(v___x_4673_, v_prec_4667_);
                return v___x_4674_;
            }
            2 => {
                v___x_4678_ = l_Lean_IR_instReprArg_repr___closed__4;
                v___x_4679_ = l_Lean_IR_instReprVarId_repr___redArg(v_id_4675_);
                v___x_4680_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4680_, 0, v___x_4678_);
                lean_ctor_set(v___x_4680_, 1, v___x_4679_);
                lean_inc(v___y_4677_);
                v___x_4681_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4681_, 0, v___y_4677_);
                lean_ctor_set(v___x_4681_, 1, v___x_4680_);
                v___x_4682_ = 0;
                v___x_4683_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4683_, 0, v___x_4681_);
                lean_ctor_set_uint8(
                    v___x_4683_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4682_,
                );
                v___x_4684_ = l_Repr_addAppParen(v___x_4683_, v_prec_4667_);
                return v___x_4684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_instReprArg_repr___boxed(
    mut v_x_4693_: *mut LeanObject,
    mut v_prec_4694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4695_: *mut LeanObject = core::ptr::null_mut();
    v_res_4695_ = l_Lean_IR_instReprArg_repr(v_x_4693_, v_prec_4694_);
    lean_dec(v_prec_4694_);
    return v_res_4695_;
}
pub unsafe fn l_Lean_IR_Arg_beq(
    mut v_x_4698_: *mut LeanObject,
    mut v_x_4699_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4698_) == 0 {
        if lean_obj_tag(v_x_4699_) == 0 {
            let mut v_id_4700_: *mut LeanObject = core::ptr::null_mut();
            let mut v_id_4701_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4702_: u8 = 0;
            v_id_4700_ = lean_ctor_get(v_x_4698_, 0);
            v_id_4701_ = lean_ctor_get(v_x_4699_, 0);
            v___x_4702_ = lean_nat_dec_eq(v_id_4700_, v_id_4701_);
            return v___x_4702_;
        } else {
            let mut v___x_4703_: u8 = 0;
            v___x_4703_ = 0;
            return v___x_4703_;
        }
    } else {
        if lean_obj_tag(v_x_4699_) == 1 {
            let mut v___x_4704_: u8 = 0;
            v___x_4704_ = 1;
            return v___x_4704_;
        } else {
            let mut v___x_4705_: u8 = 0;
            v___x_4705_ = 0;
            return v___x_4705_;
        }
    }
}
pub unsafe fn l_Lean_IR_Arg_beq___boxed(
    mut v_x_4706_: *mut LeanObject,
    mut v_x_4707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4708_: u8 = 0;
    let mut v_r_4709_: *mut LeanObject = core::ptr::null_mut();
    v_res_4708_ = l_Lean_IR_Arg_beq(v_x_4706_, v_x_4707_);
    lean_dec(v_x_4707_);
    lean_dec(v_x_4706_);
    v_r_4709_ = lean_box((v_res_4708_) as usize);
    return v_r_4709_;
}
pub unsafe fn l_Lean_IR_LitVal_ctorIdx(mut v_x_4710_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_4710_) == 0 {
        let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
        v___x_4711_ = lean_unsigned_to_nat(0);
        return v___x_4711_;
    } else {
        let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
        v___x_4712_ = lean_unsigned_to_nat(1);
        return v___x_4712_;
    }
}
pub unsafe fn l_Lean_IR_LitVal_ctorIdx___boxed(mut v_x_4713_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4714_: *mut LeanObject = core::ptr::null_mut();
    v_res_4714_ = l_Lean_IR_LitVal_ctorIdx(v_x_4713_);
    lean_dec_ref(v_x_4713_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_IR_LitVal_ctorElim___redArg(
    mut v_t_4715_: *mut LeanObject,
    mut v_k_4716_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4715_) == 0 {
        let mut v_v_4717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
        v_v_4717_ = lean_ctor_get(v_t_4715_, 0);
        lean_inc(v_v_4717_);
        lean_dec_ref_known(v_t_4715_, 1);
        v___x_4718_ = lean_apply_1(v_k_4716_, v_v_4717_);
        return v___x_4718_;
    } else {
        let mut v_v_4719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
        v_v_4719_ = lean_ctor_get(v_t_4715_, 0);
        lean_inc_ref(v_v_4719_);
        lean_dec_ref_known(v_t_4715_, 1);
        v___x_4720_ = lean_apply_1(v_k_4716_, v_v_4719_);
        return v___x_4720_;
    }
}
pub unsafe fn l_Lean_IR_LitVal_ctorElim(
    mut v_motive_4721_: *mut LeanObject,
    mut v_ctorIdx_4722_: *mut LeanObject,
    mut v_t_4723_: *mut LeanObject,
    mut v_h_4724_: *mut LeanObject,
    mut v_k_4725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    v___x_4726_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4723_, v_k_4725_);
    return v___x_4726_;
}
pub unsafe fn l_Lean_IR_LitVal_ctorElim___boxed(
    mut v_motive_4727_: *mut LeanObject,
    mut v_ctorIdx_4728_: *mut LeanObject,
    mut v_t_4729_: *mut LeanObject,
    mut v_h_4730_: *mut LeanObject,
    mut v_k_4731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4732_: *mut LeanObject = core::ptr::null_mut();
    v_res_4732_ = l_Lean_IR_LitVal_ctorElim(
        v_motive_4727_,
        v_ctorIdx_4728_,
        v_t_4729_,
        v_h_4730_,
        v_k_4731_,
    );
    lean_dec(v_ctorIdx_4728_);
    return v_res_4732_;
}
pub unsafe fn l_Lean_IR_LitVal_num_elim___redArg(
    mut v_t_4733_: *mut LeanObject,
    mut v_num_4734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    v___x_4735_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4733_, v_num_4734_);
    return v___x_4735_;
}
pub unsafe fn l_Lean_IR_LitVal_num_elim(
    mut v_motive_4736_: *mut LeanObject,
    mut v_t_4737_: *mut LeanObject,
    mut v_h_4738_: *mut LeanObject,
    mut v_num_4739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    v___x_4740_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4737_, v_num_4739_);
    return v___x_4740_;
}
pub unsafe fn l_Lean_IR_LitVal_str_elim___redArg(
    mut v_t_4741_: *mut LeanObject,
    mut v_str_4742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    v___x_4743_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4741_, v_str_4742_);
    return v___x_4743_;
}
pub unsafe fn l_Lean_IR_LitVal_str_elim(
    mut v_motive_4744_: *mut LeanObject,
    mut v_t_4745_: *mut LeanObject,
    mut v_h_4746_: *mut LeanObject,
    mut v_str_4747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    v___x_4748_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4745_, v_str_4747_);
    return v___x_4748_;
}
pub unsafe fn l_Lean_IR_instBEqLitVal_beq(
    mut v_x_4753_: *mut LeanObject,
    mut v_x_4754_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4753_) == 0 {
        if lean_obj_tag(v_x_4754_) == 0 {
            let mut v_v_4755_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4756_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4757_: u8 = 0;
            v_v_4755_ = lean_ctor_get(v_x_4753_, 0);
            v_v_4756_ = lean_ctor_get(v_x_4754_, 0);
            v___x_4757_ = lean_nat_dec_eq(v_v_4755_, v_v_4756_);
            return v___x_4757_;
        } else {
            let mut v___x_4758_: u8 = 0;
            v___x_4758_ = 0;
            return v___x_4758_;
        }
    } else {
        if lean_obj_tag(v_x_4754_) == 1 {
            let mut v_v_4759_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_4760_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4761_: u8 = 0;
            v_v_4759_ = lean_ctor_get(v_x_4753_, 0);
            v_v_4760_ = lean_ctor_get(v_x_4754_, 0);
            v___x_4761_ = lean_string_dec_eq(v_v_4759_, v_v_4760_);
            return v___x_4761_;
        } else {
            let mut v___x_4762_: u8 = 0;
            v___x_4762_ = 0;
            return v___x_4762_;
        }
    }
}
pub unsafe fn l_Lean_IR_instBEqLitVal_beq___boxed(
    mut v_x_4763_: *mut LeanObject,
    mut v_x_4764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4765_: u8 = 0;
    let mut v_r_4766_: *mut LeanObject = core::ptr::null_mut();
    v_res_4765_ = l_Lean_IR_instBEqLitVal_beq(v_x_4763_, v_x_4764_);
    lean_dec_ref(v_x_4764_);
    lean_dec_ref(v_x_4763_);
    v_r_4766_ = lean_box((v_res_4765_) as usize);
    return v_r_4766_;
}
pub unsafe fn l_Lean_IR_instBEqCtorInfo_beq(
    mut v_x_4774_: *mut LeanObject,
    mut v_x_4775_: *mut LeanObject,
) -> u8 {
    let mut v_name_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    v_name_4776_ = lean_ctor_get(v_x_4774_, 0);
    v_cidx_4777_ = lean_ctor_get(v_x_4774_, 1);
    v_size_4778_ = lean_ctor_get(v_x_4774_, 2);
    v_usize_4779_ = lean_ctor_get(v_x_4774_, 3);
    v_ssize_4780_ = lean_ctor_get(v_x_4774_, 4);
    v_name_4781_ = lean_ctor_get(v_x_4775_, 0);
    v_cidx_4782_ = lean_ctor_get(v_x_4775_, 1);
    v_size_4783_ = lean_ctor_get(v_x_4775_, 2);
    v_usize_4784_ = lean_ctor_get(v_x_4775_, 3);
    v_ssize_4785_ = lean_ctor_get(v_x_4775_, 4);
    v___x_4786_ = lean_name_eq(v_name_4776_, v_name_4781_);
    if v___x_4786_ == 0 {
        return v___x_4786_;
    } else {
        let mut v___x_4787_: u8 = 0;
        v___x_4787_ = lean_nat_dec_eq(v_cidx_4777_, v_cidx_4782_);
        if v___x_4787_ == 0 {
            return v___x_4787_;
        } else {
            let mut v___x_4788_: u8 = 0;
            v___x_4788_ = lean_nat_dec_eq(v_size_4778_, v_size_4783_);
            if v___x_4788_ == 0 {
                return v___x_4788_;
            } else {
                let mut v___x_4789_: u8 = 0;
                v___x_4789_ = lean_nat_dec_eq(v_usize_4779_, v_usize_4784_);
                if v___x_4789_ == 0 {
                    return v___x_4789_;
                } else {
                    let mut v___x_4790_: u8 = 0;
                    v___x_4790_ = lean_nat_dec_eq(v_ssize_4780_, v_ssize_4785_);
                    return v___x_4790_;
                }
            }
        }
    }
}
pub unsafe fn l_Lean_IR_instBEqCtorInfo_beq___boxed(
    mut v_x_4791_: *mut LeanObject,
    mut v_x_4792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4793_: u8 = 0;
    let mut v_r_4794_: *mut LeanObject = core::ptr::null_mut();
    v_res_4793_ = l_Lean_IR_instBEqCtorInfo_beq(v_x_4791_, v_x_4792_);
    lean_dec_ref(v_x_4792_);
    lean_dec_ref(v_x_4791_);
    v_r_4794_ = lean_box((v_res_4793_) as usize);
    return v_r_4794_;
}
pub unsafe fn _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    v___x_4806_ = lean_unsigned_to_nat(8);
    v___x_4807_ = lean_nat_to_int(v___x_4806_);
    return v___x_4807_;
}
pub unsafe fn _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    v___x_4817_ = lean_unsigned_to_nat(9);
    v___x_4818_ = lean_nat_to_int(v___x_4817_);
    return v___x_4818_;
}
pub unsafe fn l_Lean_IR_instReprCtorInfo_repr___redArg(
    mut v_x_4822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: u8 = 0;
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    v_name_4823_ = lean_ctor_get(v_x_4822_, 0);
    lean_inc(v_name_4823_);
    v_cidx_4824_ = lean_ctor_get(v_x_4822_, 1);
    lean_inc(v_cidx_4824_);
    v_size_4825_ = lean_ctor_get(v_x_4822_, 2);
    lean_inc(v_size_4825_);
    v_usize_4826_ = lean_ctor_get(v_x_4822_, 3);
    lean_inc(v_usize_4826_);
    v_ssize_4827_ = lean_ctor_get(v_x_4822_, 4);
    lean_inc(v_ssize_4827_);
    lean_dec_ref(v_x_4822_);
    v___x_4828_ = l_Lean_IR_instReprVarId_repr___redArg___closed__5;
    v___x_4829_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3;
    v___x_4830_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4_once),
        _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4,
    );
    v___x_4831_ = lean_unsigned_to_nat(0);
    v___x_4832_ = l_Lean_Name_reprPrec(v_name_4823_, v___x_4831_);
    v___x_4833_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4833_, 0, v___x_4830_);
    lean_ctor_set(v___x_4833_, 1, v___x_4832_);
    v___x_4834_ = 0;
    v___x_4835_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4835_, 0, v___x_4833_);
    lean_ctor_set_uint8(
        v___x_4835_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4836_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4836_, 0, v___x_4829_);
    lean_ctor_set(v___x_4836_, 1, v___x_4835_);
    v___x_4837_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2;
    v___x_4838_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4838_, 0, v___x_4836_);
    lean_ctor_set(v___x_4838_, 1, v___x_4837_);
    v___x_4839_ = lean_box(1);
    v___x_4840_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4840_, 0, v___x_4838_);
    lean_ctor_set(v___x_4840_, 1, v___x_4839_);
    v___x_4841_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6;
    v___x_4842_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4842_, 0, v___x_4840_);
    lean_ctor_set(v___x_4842_, 1, v___x_4841_);
    v___x_4843_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4843_, 0, v___x_4842_);
    lean_ctor_set(v___x_4843_, 1, v___x_4828_);
    v___x_4844_ = l_Nat_reprFast(v_cidx_4824_);
    v___x_4845_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4845_, 0, v___x_4844_);
    v___x_4846_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4846_, 0, v___x_4830_);
    lean_ctor_set(v___x_4846_, 1, v___x_4845_);
    v___x_4847_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4847_, 0, v___x_4846_);
    lean_ctor_set_uint8(
        v___x_4847_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4848_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4848_, 0, v___x_4843_);
    lean_ctor_set(v___x_4848_, 1, v___x_4847_);
    v___x_4849_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4849_, 0, v___x_4848_);
    lean_ctor_set(v___x_4849_, 1, v___x_4837_);
    v___x_4850_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4850_, 0, v___x_4849_);
    lean_ctor_set(v___x_4850_, 1, v___x_4839_);
    v___x_4851_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8;
    v___x_4852_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4852_, 0, v___x_4850_);
    lean_ctor_set(v___x_4852_, 1, v___x_4851_);
    v___x_4853_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4853_, 0, v___x_4852_);
    lean_ctor_set(v___x_4853_, 1, v___x_4828_);
    v___x_4854_ = l_Nat_reprFast(v_size_4825_);
    v___x_4855_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4855_, 0, v___x_4854_);
    v___x_4856_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4856_, 0, v___x_4830_);
    lean_ctor_set(v___x_4856_, 1, v___x_4855_);
    v___x_4857_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4857_, 0, v___x_4856_);
    lean_ctor_set_uint8(
        v___x_4857_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4858_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4858_, 0, v___x_4853_);
    lean_ctor_set(v___x_4858_, 1, v___x_4857_);
    v___x_4859_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4859_, 0, v___x_4858_);
    lean_ctor_set(v___x_4859_, 1, v___x_4837_);
    v___x_4860_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4860_, 0, v___x_4859_);
    lean_ctor_set(v___x_4860_, 1, v___x_4839_);
    v___x_4861_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10;
    v___x_4862_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4862_, 0, v___x_4860_);
    lean_ctor_set(v___x_4862_, 1, v___x_4861_);
    v___x_4863_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4863_, 0, v___x_4862_);
    lean_ctor_set(v___x_4863_, 1, v___x_4828_);
    v___x_4864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11_once),
        _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11,
    );
    v___x_4865_ = l_Nat_reprFast(v_usize_4826_);
    v___x_4866_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4866_, 0, v___x_4865_);
    v___x_4867_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4867_, 0, v___x_4864_);
    lean_ctor_set(v___x_4867_, 1, v___x_4866_);
    v___x_4868_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4868_, 0, v___x_4867_);
    lean_ctor_set_uint8(
        v___x_4868_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4869_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4869_, 0, v___x_4863_);
    lean_ctor_set(v___x_4869_, 1, v___x_4868_);
    v___x_4870_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4870_, 0, v___x_4869_);
    lean_ctor_set(v___x_4870_, 1, v___x_4837_);
    v___x_4871_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4871_, 0, v___x_4870_);
    lean_ctor_set(v___x_4871_, 1, v___x_4839_);
    v___x_4872_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13;
    v___x_4873_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4873_, 0, v___x_4871_);
    lean_ctor_set(v___x_4873_, 1, v___x_4872_);
    v___x_4874_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4874_, 0, v___x_4873_);
    lean_ctor_set(v___x_4874_, 1, v___x_4828_);
    v___x_4875_ = l_Nat_reprFast(v_ssize_4827_);
    v___x_4876_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4876_, 0, v___x_4875_);
    v___x_4877_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4877_, 0, v___x_4864_);
    lean_ctor_set(v___x_4877_, 1, v___x_4876_);
    v___x_4878_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4878_, 0, v___x_4877_);
    lean_ctor_set_uint8(
        v___x_4878_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4879_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4879_, 0, v___x_4874_);
    lean_ctor_set(v___x_4879_, 1, v___x_4878_);
    v___x_4880_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_4881_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_4882_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4882_, 0, v___x_4881_);
    lean_ctor_set(v___x_4882_, 1, v___x_4879_);
    v___x_4883_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_4884_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_4884_, 0, v___x_4882_);
    lean_ctor_set(v___x_4884_, 1, v___x_4883_);
    v___x_4885_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_4885_, 0, v___x_4880_);
    lean_ctor_set(v___x_4885_, 1, v___x_4884_);
    v___x_4886_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_4886_, 0, v___x_4885_);
    lean_ctor_set_uint8(
        v___x_4886_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    return v___x_4886_;
}
pub unsafe fn l_Lean_IR_instReprCtorInfo_repr(
    mut v_x_4887_: *mut LeanObject,
    mut v_prec_4888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    v___x_4889_ = l_Lean_IR_instReprCtorInfo_repr___redArg(v_x_4887_);
    return v___x_4889_;
}
pub unsafe fn l_Lean_IR_instReprCtorInfo_repr___boxed(
    mut v_x_4890_: *mut LeanObject,
    mut v_prec_4891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4892_: *mut LeanObject = core::ptr::null_mut();
    v_res_4892_ = l_Lean_IR_instReprCtorInfo_repr(v_x_4890_, v_prec_4891_);
    lean_dec(v_prec_4891_);
    return v_res_4892_;
}
pub unsafe fn l_Lean_IR_CtorInfo_isRef(mut v_info_4895_: *mut LeanObject) -> u8 {
    let mut v_size_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usize_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ssize_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: u8 = 0;
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: u8 = 0;
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4896_ = lean_ctor_get(v_info_4895_, 2);
                v_usize_4897_ = lean_ctor_get(v_info_4895_, 3);
                v_ssize_4898_ = lean_ctor_get(v_info_4895_, 4);
                v___x_4903_ = lean_unsigned_to_nat(0);
                v___x_4904_ = lean_nat_dec_lt(v___x_4903_, v_size_4896_);
                if v___x_4904_ == 0 {
                    v___x_4905_ = lean_nat_dec_lt(v___x_4903_, v_usize_4897_);
                    v___y_4900_ = v___x_4905_;
                    state = 1;
                    continue;
                } else {
                    v___y_4900_ = v___x_4904_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4900_ == 0 {
                    v___x_4901_ = lean_unsigned_to_nat(0);
                    v___x_4902_ = lean_nat_dec_lt(v___x_4901_, v_ssize_4898_);
                    return v___x_4902_;
                } else {
                    return v___y_4900_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_CtorInfo_isRef___boxed(
    mut v_info_4906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4907_: u8 = 0;
    let mut v_r_4908_: *mut LeanObject = core::ptr::null_mut();
    v_res_4907_ = l_Lean_IR_CtorInfo_isRef(v_info_4906_);
    lean_dec_ref(v_info_4906_);
    v_r_4908_ = lean_box((v_res_4907_) as usize);
    return v_r_4908_;
}
pub unsafe fn l_Lean_IR_CtorInfo_isScalar(mut v_info_4909_: *mut LeanObject) -> u8 {
    let mut v___x_4910_: u8 = 0;
    v___x_4910_ = l_Lean_IR_CtorInfo_isRef(v_info_4909_);
    if v___x_4910_ == 0 {
        let mut v___x_4911_: u8 = 0;
        v___x_4911_ = 1;
        return v___x_4911_;
    } else {
        let mut v___x_4912_: u8 = 0;
        v___x_4912_ = 0;
        return v___x_4912_;
    }
}
pub unsafe fn l_Lean_IR_CtorInfo_isScalar___boxed(
    mut v_info_4913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4914_: u8 = 0;
    let mut v_r_4915_: *mut LeanObject = core::ptr::null_mut();
    v_res_4914_ = l_Lean_IR_CtorInfo_isScalar(v_info_4913_);
    lean_dec_ref(v_info_4913_);
    v_r_4915_ = lean_box((v_res_4914_) as usize);
    return v_r_4915_;
}
pub unsafe fn l_Lean_IR_CtorInfo_type(mut v_info_4916_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4917_: u8 = 0;
    v___x_4917_ = l_Lean_IR_CtorInfo_isRef(v_info_4916_);
    if v___x_4917_ == 0 {
        let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
        v___x_4918_ = lean_box(12);
        return v___x_4918_;
    } else {
        let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
        v___x_4919_ = lean_box(7);
        return v___x_4919_;
    }
}
pub unsafe fn l_Lean_IR_CtorInfo_type___boxed(
    mut v_info_4920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4921_: *mut LeanObject = core::ptr::null_mut();
    v_res_4921_ = l_Lean_IR_CtorInfo_type(v_info_4920_);
    lean_dec_ref(v_info_4920_);
    return v_res_4921_;
}
pub unsafe fn l_Lean_IR_Expr_ctorIdx(mut v_x_4922_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4922_) {
        0 => {
            let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
            v___x_4923_ = lean_unsigned_to_nat(0);
            return v___x_4923_;
        }
        1 => {
            let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
            v___x_4924_ = lean_unsigned_to_nat(1);
            return v___x_4924_;
        }
        2 => {
            let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
            v___x_4925_ = lean_unsigned_to_nat(2);
            return v___x_4925_;
        }
        3 => {
            let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
            v___x_4926_ = lean_unsigned_to_nat(3);
            return v___x_4926_;
        }
        4 => {
            let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
            v___x_4927_ = lean_unsigned_to_nat(4);
            return v___x_4927_;
        }
        5 => {
            let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
            v___x_4928_ = lean_unsigned_to_nat(5);
            return v___x_4928_;
        }
        6 => {
            let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
            v___x_4929_ = lean_unsigned_to_nat(6);
            return v___x_4929_;
        }
        7 => {
            let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
            v___x_4930_ = lean_unsigned_to_nat(7);
            return v___x_4930_;
        }
        8 => {
            let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
            v___x_4931_ = lean_unsigned_to_nat(8);
            return v___x_4931_;
        }
        9 => {
            let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
            v___x_4932_ = lean_unsigned_to_nat(9);
            return v___x_4932_;
        }
        10 => {
            let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
            v___x_4933_ = lean_unsigned_to_nat(10);
            return v___x_4933_;
        }
        11 => {
            let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
            v___x_4934_ = lean_unsigned_to_nat(11);
            return v___x_4934_;
        }
        _ => {
            let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
            v___x_4935_ = lean_unsigned_to_nat(12);
            return v___x_4935_;
        }
    }
}
pub unsafe fn l_Lean_IR_Expr_ctorIdx___boxed(mut v_x_4936_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_4937_: *mut LeanObject = core::ptr::null_mut();
    v_res_4937_ = l_Lean_IR_Expr_ctorIdx(v_x_4936_);
    lean_dec_ref(v_x_4936_);
    return v_res_4937_;
}
pub unsafe fn l_Lean_IR_Expr_ctorElim___redArg(
    mut v_t_4938_: *mut LeanObject,
    mut v_k_4939_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4938_) {
        0 => {
            let mut v_i_4940_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ys_4941_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
            v_i_4940_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc_ref(v_i_4940_);
            v_ys_4941_ = lean_ctor_get(v_t_4938_, 1);
            lean_inc_ref(v_ys_4941_);
            lean_dec_ref_known(v_t_4938_, 2);
            v___x_4942_ = lean_apply_2(v_k_4939_, v_i_4940_, v_ys_4941_);
            return v___x_4942_;
        }
        2 => {
            let mut v_x_4943_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_4944_: *mut LeanObject = core::ptr::null_mut();
            let mut v_updtHeader_4945_: u8 = 0;
            let mut v_ys_4946_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
            v_x_4943_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_x_4943_);
            v_i_4944_ = lean_ctor_get(v_t_4938_, 1);
            lean_inc_ref(v_i_4944_);
            v_updtHeader_4945_ = lean_ctor_get_uint8(
                v_t_4938_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_ys_4946_ = lean_ctor_get(v_t_4938_, 2);
            lean_inc_ref(v_ys_4946_);
            lean_dec_ref_known(v_t_4938_, 3);
            v___x_4947_ = lean_box((v_updtHeader_4945_) as usize);
            v___x_4948_ = lean_apply_4(v_k_4939_, v_x_4943_, v_i_4944_, v___x_4947_, v_ys_4946_);
            return v___x_4948_;
        }
        5 => {
            let mut v_n_4949_: *mut LeanObject = core::ptr::null_mut();
            let mut v_offset_4950_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_4951_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
            v_n_4949_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_n_4949_);
            v_offset_4950_ = lean_ctor_get(v_t_4938_, 1);
            lean_inc(v_offset_4950_);
            v_x_4951_ = lean_ctor_get(v_t_4938_, 2);
            lean_inc(v_x_4951_);
            lean_dec_ref_known(v_t_4938_, 3);
            v___x_4952_ = lean_apply_3(v_k_4939_, v_n_4949_, v_offset_4950_, v_x_4951_);
            return v___x_4952_;
        }
        6 => {
            let mut v_c_4953_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ys_4954_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
            v_c_4953_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_c_4953_);
            v_ys_4954_ = lean_ctor_get(v_t_4938_, 1);
            lean_inc_ref(v_ys_4954_);
            lean_dec_ref_known(v_t_4938_, 2);
            v___x_4955_ = lean_apply_2(v_k_4939_, v_c_4953_, v_ys_4954_);
            return v___x_4955_;
        }
        7 => {
            let mut v_c_4956_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ys_4957_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
            v_c_4956_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_c_4956_);
            v_ys_4957_ = lean_ctor_get(v_t_4938_, 1);
            lean_inc_ref(v_ys_4957_);
            lean_dec_ref_known(v_t_4938_, 2);
            v___x_4958_ = lean_apply_2(v_k_4939_, v_c_4956_, v_ys_4957_);
            return v___x_4958_;
        }
        8 => {
            let mut v_x_4959_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ys_4960_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
            v_x_4959_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_x_4959_);
            v_ys_4960_ = lean_ctor_get(v_t_4938_, 1);
            lean_inc_ref(v_ys_4960_);
            lean_dec_ref_known(v_t_4938_, 2);
            v___x_4961_ = lean_apply_2(v_k_4939_, v_x_4959_, v_ys_4960_);
            return v___x_4961_;
        }
        10 => {
            let mut v_x_4962_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
            v_x_4962_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_x_4962_);
            lean_dec_ref_known(v_t_4938_, 1);
            v___x_4963_ = lean_apply_1(v_k_4939_, v_x_4962_);
            return v___x_4963_;
        }
        11 => {
            let mut v_v_4964_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
            v_v_4964_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc_ref(v_v_4964_);
            lean_dec_ref_known(v_t_4938_, 1);
            v___x_4965_ = lean_apply_1(v_k_4939_, v_v_4964_);
            return v___x_4965_;
        }
        12 => {
            let mut v_x_4966_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
            v_x_4966_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_x_4966_);
            lean_dec_ref_known(v_t_4938_, 1);
            v___x_4967_ = lean_apply_1(v_k_4939_, v_x_4966_);
            return v___x_4967_;
        }
        _ => {
            let mut v_n_4968_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_4969_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
            v_n_4968_ = lean_ctor_get(v_t_4938_, 0);
            lean_inc(v_n_4968_);
            v_x_4969_ = lean_ctor_get(v_t_4938_, 1);
            lean_inc(v_x_4969_);
            lean_dec_ref(v_t_4938_);
            v___x_4970_ = lean_apply_2(v_k_4939_, v_n_4968_, v_x_4969_);
            return v___x_4970_;
        }
    }
}
pub unsafe fn l_Lean_IR_Expr_ctorElim(
    mut v_motive_4971_: *mut LeanObject,
    mut v_ctorIdx_4972_: *mut LeanObject,
    mut v_t_4973_: *mut LeanObject,
    mut v_h_4974_: *mut LeanObject,
    mut v_k_4975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    v___x_4976_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4973_, v_k_4975_);
    return v___x_4976_;
}
pub unsafe fn l_Lean_IR_Expr_ctorElim___boxed(
    mut v_motive_4977_: *mut LeanObject,
    mut v_ctorIdx_4978_: *mut LeanObject,
    mut v_t_4979_: *mut LeanObject,
    mut v_h_4980_: *mut LeanObject,
    mut v_k_4981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4982_: *mut LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Lean_IR_Expr_ctorElim(
        v_motive_4977_,
        v_ctorIdx_4978_,
        v_t_4979_,
        v_h_4980_,
        v_k_4981_,
    );
    lean_dec(v_ctorIdx_4978_);
    return v_res_4982_;
}
pub unsafe fn l_Lean_IR_Expr_ctor_elim___redArg(
    mut v_t_4983_: *mut LeanObject,
    mut v_ctor_4984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    v___x_4985_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4983_, v_ctor_4984_);
    return v___x_4985_;
}
pub unsafe fn l_Lean_IR_Expr_ctor_elim(
    mut v_motive_4986_: *mut LeanObject,
    mut v_t_4987_: *mut LeanObject,
    mut v_h_4988_: *mut LeanObject,
    mut v_ctor_4989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    v___x_4990_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4987_, v_ctor_4989_);
    return v___x_4990_;
}
pub unsafe fn l_Lean_IR_Expr_reset_elim___redArg(
    mut v_t_4991_: *mut LeanObject,
    mut v_reset_4992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    v___x_4993_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4991_, v_reset_4992_);
    return v___x_4993_;
}
pub unsafe fn l_Lean_IR_Expr_reset_elim(
    mut v_motive_4994_: *mut LeanObject,
    mut v_t_4995_: *mut LeanObject,
    mut v_h_4996_: *mut LeanObject,
    mut v_reset_4997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    v___x_4998_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4995_, v_reset_4997_);
    return v___x_4998_;
}
pub unsafe fn l_Lean_IR_Expr_reuse_elim___redArg(
    mut v_t_4999_: *mut LeanObject,
    mut v_reuse_5000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    v___x_5001_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4999_, v_reuse_5000_);
    return v___x_5001_;
}
pub unsafe fn l_Lean_IR_Expr_reuse_elim(
    mut v_motive_5002_: *mut LeanObject,
    mut v_t_5003_: *mut LeanObject,
    mut v_h_5004_: *mut LeanObject,
    mut v_reuse_5005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    v___x_5006_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5003_, v_reuse_5005_);
    return v___x_5006_;
}
pub unsafe fn l_Lean_IR_Expr_proj_elim___redArg(
    mut v_t_5007_: *mut LeanObject,
    mut v_proj_5008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    v___x_5009_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5007_, v_proj_5008_);
    return v___x_5009_;
}
pub unsafe fn l_Lean_IR_Expr_proj_elim(
    mut v_motive_5010_: *mut LeanObject,
    mut v_t_5011_: *mut LeanObject,
    mut v_h_5012_: *mut LeanObject,
    mut v_proj_5013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    v___x_5014_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5011_, v_proj_5013_);
    return v___x_5014_;
}
pub unsafe fn l_Lean_IR_Expr_uproj_elim___redArg(
    mut v_t_5015_: *mut LeanObject,
    mut v_uproj_5016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    v___x_5017_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5015_, v_uproj_5016_);
    return v___x_5017_;
}
pub unsafe fn l_Lean_IR_Expr_uproj_elim(
    mut v_motive_5018_: *mut LeanObject,
    mut v_t_5019_: *mut LeanObject,
    mut v_h_5020_: *mut LeanObject,
    mut v_uproj_5021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    v___x_5022_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5019_, v_uproj_5021_);
    return v___x_5022_;
}
pub unsafe fn l_Lean_IR_Expr_sproj_elim___redArg(
    mut v_t_5023_: *mut LeanObject,
    mut v_sproj_5024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    v___x_5025_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5023_, v_sproj_5024_);
    return v___x_5025_;
}
pub unsafe fn l_Lean_IR_Expr_sproj_elim(
    mut v_motive_5026_: *mut LeanObject,
    mut v_t_5027_: *mut LeanObject,
    mut v_h_5028_: *mut LeanObject,
    mut v_sproj_5029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    v___x_5030_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5027_, v_sproj_5029_);
    return v___x_5030_;
}
pub unsafe fn l_Lean_IR_Expr_fap_elim___redArg(
    mut v_t_5031_: *mut LeanObject,
    mut v_fap_5032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5031_, v_fap_5032_);
    return v___x_5033_;
}
pub unsafe fn l_Lean_IR_Expr_fap_elim(
    mut v_motive_5034_: *mut LeanObject,
    mut v_t_5035_: *mut LeanObject,
    mut v_h_5036_: *mut LeanObject,
    mut v_fap_5037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    v___x_5038_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5035_, v_fap_5037_);
    return v___x_5038_;
}
pub unsafe fn l_Lean_IR_Expr_pap_elim___redArg(
    mut v_t_5039_: *mut LeanObject,
    mut v_pap_5040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    v___x_5041_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5039_, v_pap_5040_);
    return v___x_5041_;
}
pub unsafe fn l_Lean_IR_Expr_pap_elim(
    mut v_motive_5042_: *mut LeanObject,
    mut v_t_5043_: *mut LeanObject,
    mut v_h_5044_: *mut LeanObject,
    mut v_pap_5045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    v___x_5046_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5043_, v_pap_5045_);
    return v___x_5046_;
}
pub unsafe fn l_Lean_IR_Expr_ap_elim___redArg(
    mut v_t_5047_: *mut LeanObject,
    mut v_ap_5048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    v___x_5049_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5047_, v_ap_5048_);
    return v___x_5049_;
}
pub unsafe fn l_Lean_IR_Expr_ap_elim(
    mut v_motive_5050_: *mut LeanObject,
    mut v_t_5051_: *mut LeanObject,
    mut v_h_5052_: *mut LeanObject,
    mut v_ap_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    v___x_5054_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5051_, v_ap_5053_);
    return v___x_5054_;
}
pub unsafe fn l_Lean_IR_Expr_box_elim___redArg(
    mut v_t_5055_: *mut LeanObject,
    mut v_box_5056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    v___x_5057_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5055_, v_box_5056_);
    return v___x_5057_;
}
pub unsafe fn l_Lean_IR_Expr_box_elim(
    mut v_motive_5058_: *mut LeanObject,
    mut v_t_5059_: *mut LeanObject,
    mut v_h_5060_: *mut LeanObject,
    mut v_box_5061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    v___x_5062_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5059_, v_box_5061_);
    return v___x_5062_;
}
pub unsafe fn l_Lean_IR_Expr_unbox_elim___redArg(
    mut v_t_5063_: *mut LeanObject,
    mut v_unbox_5064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v___x_5065_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5063_, v_unbox_5064_);
    return v___x_5065_;
}
pub unsafe fn l_Lean_IR_Expr_unbox_elim(
    mut v_motive_5066_: *mut LeanObject,
    mut v_t_5067_: *mut LeanObject,
    mut v_h_5068_: *mut LeanObject,
    mut v_unbox_5069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    v___x_5070_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5067_, v_unbox_5069_);
    return v___x_5070_;
}
pub unsafe fn l_Lean_IR_Expr_lit_elim___redArg(
    mut v_t_5071_: *mut LeanObject,
    mut v_lit_5072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    v___x_5073_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5071_, v_lit_5072_);
    return v___x_5073_;
}
pub unsafe fn l_Lean_IR_Expr_lit_elim(
    mut v_motive_5074_: *mut LeanObject,
    mut v_t_5075_: *mut LeanObject,
    mut v_h_5076_: *mut LeanObject,
    mut v_lit_5077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    v___x_5078_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5075_, v_lit_5077_);
    return v___x_5078_;
}
pub unsafe fn l_Lean_IR_Expr_isShared_elim___redArg(
    mut v_t_5079_: *mut LeanObject,
    mut v_isShared_5080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    v___x_5081_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5079_, v_isShared_5080_);
    return v___x_5081_;
}
pub unsafe fn l_Lean_IR_Expr_isShared_elim(
    mut v_motive_5082_: *mut LeanObject,
    mut v_t_5083_: *mut LeanObject,
    mut v_h_5084_: *mut LeanObject,
    mut v_isShared_5085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5083_, v_isShared_5085_);
    return v___x_5086_;
}
pub unsafe fn _init_l_Lean_IR_instReprParam_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    v___x_5109_ = lean_unsigned_to_nat(5);
    v___x_5110_ = lean_nat_to_int(v___x_5109_);
    return v___x_5110_;
}
pub unsafe fn _init_l_Lean_IR_instReprParam_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    v___x_5114_ = lean_unsigned_to_nat(10);
    v___x_5115_ = lean_nat_to_int(v___x_5114_);
    return v___x_5115_;
}
pub unsafe fn _init_l_Lean_IR_instReprParam_repr___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    v___x_5119_ = lean_unsigned_to_nat(6);
    v___x_5120_ = lean_nat_to_int(v___x_5119_);
    return v___x_5120_;
}
pub unsafe fn l_Lean_IR_instReprParam_repr___redArg(
    mut v_x_5121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_5123_: u8 = 0;
    let mut v_ty_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: u8 = 0;
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    v_x_5122_ = lean_ctor_get(v_x_5121_, 0);
    lean_inc(v_x_5122_);
    v_borrow_5123_ = lean_ctor_get_uint8(
        v_x_5121_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_ty_5124_ = lean_ctor_get(v_x_5121_, 1);
    lean_inc(v_ty_5124_);
    lean_dec_ref(v_x_5121_);
    v___x_5125_ = l_Lean_IR_instReprVarId_repr___redArg___closed__5;
    v___x_5126_ = l_Lean_IR_instReprParam_repr___redArg___closed__3;
    v___x_5127_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__4_once),
        _init_l_Lean_IR_instReprParam_repr___redArg___closed__4,
    );
    v___x_5128_ = lean_unsigned_to_nat(0);
    v___x_5129_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_5122_);
    v___x_5130_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5130_, 0, v___x_5127_);
    lean_ctor_set(v___x_5130_, 1, v___x_5129_);
    v___x_5131_ = 0;
    v___x_5132_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5132_, 0, v___x_5130_);
    lean_ctor_set_uint8(
        v___x_5132_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    v___x_5133_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5133_, 0, v___x_5126_);
    lean_ctor_set(v___x_5133_, 1, v___x_5132_);
    v___x_5134_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2;
    v___x_5135_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5135_, 0, v___x_5133_);
    lean_ctor_set(v___x_5135_, 1, v___x_5134_);
    v___x_5136_ = lean_box(1);
    v___x_5137_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5137_, 0, v___x_5135_);
    lean_ctor_set(v___x_5137_, 1, v___x_5136_);
    v___x_5138_ = l_Lean_IR_instReprParam_repr___redArg___closed__6;
    v___x_5139_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5139_, 0, v___x_5137_);
    lean_ctor_set(v___x_5139_, 1, v___x_5138_);
    v___x_5140_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5140_, 0, v___x_5139_);
    lean_ctor_set(v___x_5140_, 1, v___x_5125_);
    v___x_5141_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__7_once),
        _init_l_Lean_IR_instReprParam_repr___redArg___closed__7,
    );
    v___x_5142_ = l_Bool_repr___redArg(v_borrow_5123_);
    v___x_5143_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5143_, 0, v___x_5141_);
    lean_ctor_set(v___x_5143_, 1, v___x_5142_);
    v___x_5144_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5144_, 0, v___x_5143_);
    lean_ctor_set_uint8(
        v___x_5144_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    v___x_5145_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5145_, 0, v___x_5140_);
    lean_ctor_set(v___x_5145_, 1, v___x_5144_);
    v___x_5146_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5146_, 0, v___x_5145_);
    lean_ctor_set(v___x_5146_, 1, v___x_5134_);
    v___x_5147_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5147_, 0, v___x_5146_);
    lean_ctor_set(v___x_5147_, 1, v___x_5136_);
    v___x_5148_ = l_Lean_IR_instReprParam_repr___redArg___closed__9;
    v___x_5149_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5149_, 0, v___x_5147_);
    lean_ctor_set(v___x_5149_, 1, v___x_5148_);
    v___x_5150_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5150_, 0, v___x_5149_);
    lean_ctor_set(v___x_5150_, 1, v___x_5125_);
    v___x_5151_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprParam_repr___redArg___closed__10,
    );
    v___x_5152_ = l_Lean_IR_instReprIRType_repr(v_ty_5124_, v___x_5128_);
    v___x_5153_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5153_, 0, v___x_5151_);
    lean_ctor_set(v___x_5153_, 1, v___x_5152_);
    v___x_5154_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5154_, 0, v___x_5153_);
    lean_ctor_set_uint8(
        v___x_5154_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    v___x_5155_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5155_, 0, v___x_5150_);
    lean_ctor_set(v___x_5155_, 1, v___x_5154_);
    v___x_5156_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_5157_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_5158_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5158_, 0, v___x_5157_);
    lean_ctor_set(v___x_5158_, 1, v___x_5155_);
    v___x_5159_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_5160_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5160_, 0, v___x_5158_);
    lean_ctor_set(v___x_5160_, 1, v___x_5159_);
    v___x_5161_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5161_, 0, v___x_5156_);
    lean_ctor_set(v___x_5161_, 1, v___x_5160_);
    v___x_5162_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5162_, 0, v___x_5161_);
    lean_ctor_set_uint8(
        v___x_5162_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    return v___x_5162_;
}
pub unsafe fn l_Lean_IR_instReprParam_repr(
    mut v_x_5163_: *mut LeanObject,
    mut v_prec_5164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    v___x_5165_ = l_Lean_IR_instReprParam_repr___redArg(v_x_5163_);
    return v___x_5165_;
}
pub unsafe fn l_Lean_IR_instReprParam_repr___boxed(
    mut v_x_5166_: *mut LeanObject,
    mut v_prec_5167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5168_: *mut LeanObject = core::ptr::null_mut();
    v_res_5168_ = l_Lean_IR_instReprParam_repr(v_x_5166_, v_prec_5167_);
    lean_dec(v_prec_5167_);
    return v_res_5168_;
}
pub unsafe fn l_Lean_IR_Alt_ctorIdx(mut v_x_5171_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_5171_) == 0 {
        let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
        v___x_5172_ = lean_unsigned_to_nat(0);
        return v___x_5172_;
    } else {
        let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
        v___x_5173_ = lean_unsigned_to_nat(1);
        return v___x_5173_;
    }
}
pub unsafe fn l_Lean_IR_Alt_ctorIdx___boxed(mut v_x_5174_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5175_: *mut LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_IR_Alt_ctorIdx(v_x_5174_);
    lean_dec_ref(v_x_5174_);
    return v_res_5175_;
}
pub unsafe fn l_Lean_IR_Alt_ctorElim___redArg(
    mut v_t_5176_: *mut LeanObject,
    mut v_k_5177_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5176_) == 0 {
        let mut v_info_5178_: *mut LeanObject = core::ptr::null_mut();
        let mut v_b_5179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
        v_info_5178_ = lean_ctor_get(v_t_5176_, 0);
        lean_inc_ref(v_info_5178_);
        v_b_5179_ = lean_ctor_get(v_t_5176_, 1);
        lean_inc(v_b_5179_);
        lean_dec_ref_known(v_t_5176_, 2);
        v___x_5180_ = lean_apply_2(v_k_5177_, v_info_5178_, v_b_5179_);
        return v___x_5180_;
    } else {
        let mut v_b_5181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
        v_b_5181_ = lean_ctor_get(v_t_5176_, 0);
        lean_inc(v_b_5181_);
        lean_dec_ref_known(v_t_5176_, 1);
        v___x_5182_ = lean_apply_1(v_k_5177_, v_b_5181_);
        return v___x_5182_;
    }
}
pub unsafe fn l_Lean_IR_Alt_ctorElim(
    mut v_motive__1_5183_: *mut LeanObject,
    mut v_ctorIdx_5184_: *mut LeanObject,
    mut v_t_5185_: *mut LeanObject,
    mut v_h_5186_: *mut LeanObject,
    mut v_k_5187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    v___x_5188_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5185_, v_k_5187_);
    return v___x_5188_;
}
pub unsafe fn l_Lean_IR_Alt_ctorElim___boxed(
    mut v_motive__1_5189_: *mut LeanObject,
    mut v_ctorIdx_5190_: *mut LeanObject,
    mut v_t_5191_: *mut LeanObject,
    mut v_h_5192_: *mut LeanObject,
    mut v_k_5193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5194_: *mut LeanObject = core::ptr::null_mut();
    v_res_5194_ = l_Lean_IR_Alt_ctorElim(
        v_motive__1_5189_,
        v_ctorIdx_5190_,
        v_t_5191_,
        v_h_5192_,
        v_k_5193_,
    );
    lean_dec(v_ctorIdx_5190_);
    return v_res_5194_;
}
pub unsafe fn l_Lean_IR_Alt_ctor_elim___redArg(
    mut v_t_5195_: *mut LeanObject,
    mut v_ctor_5196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    v___x_5197_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5195_, v_ctor_5196_);
    return v___x_5197_;
}
pub unsafe fn l_Lean_IR_Alt_ctor_elim(
    mut v_motive__1_5198_: *mut LeanObject,
    mut v_t_5199_: *mut LeanObject,
    mut v_h_5200_: *mut LeanObject,
    mut v_ctor_5201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    v___x_5202_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5199_, v_ctor_5201_);
    return v___x_5202_;
}
pub unsafe fn l_Lean_IR_Alt_default_elim___redArg(
    mut v_t_5203_: *mut LeanObject,
    mut v_default_5204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    v___x_5205_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5203_, v_default_5204_);
    return v___x_5205_;
}
pub unsafe fn l_Lean_IR_Alt_default_elim(
    mut v_motive__1_5206_: *mut LeanObject,
    mut v_t_5207_: *mut LeanObject,
    mut v_h_5208_: *mut LeanObject,
    mut v_default_5209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    v___x_5210_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5207_, v_default_5209_);
    return v___x_5210_;
}
pub unsafe fn l_Lean_IR_FnBody_ctorIdx(mut v_x_5211_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_5211_) {
        0 => {
            let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
            v___x_5212_ = lean_unsigned_to_nat(0);
            return v___x_5212_;
        }
        1 => {
            let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
            v___x_5213_ = lean_unsigned_to_nat(1);
            return v___x_5213_;
        }
        2 => {
            let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
            v___x_5214_ = lean_unsigned_to_nat(2);
            return v___x_5214_;
        }
        3 => {
            let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
            v___x_5215_ = lean_unsigned_to_nat(3);
            return v___x_5215_;
        }
        4 => {
            let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
            v___x_5216_ = lean_unsigned_to_nat(4);
            return v___x_5216_;
        }
        5 => {
            let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
            v___x_5217_ = lean_unsigned_to_nat(5);
            return v___x_5217_;
        }
        6 => {
            let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
            v___x_5218_ = lean_unsigned_to_nat(6);
            return v___x_5218_;
        }
        7 => {
            let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
            v___x_5219_ = lean_unsigned_to_nat(7);
            return v___x_5219_;
        }
        8 => {
            let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
            v___x_5220_ = lean_unsigned_to_nat(8);
            return v___x_5220_;
        }
        9 => {
            let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
            v___x_5221_ = lean_unsigned_to_nat(9);
            return v___x_5221_;
        }
        10 => {
            let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
            v___x_5222_ = lean_unsigned_to_nat(10);
            return v___x_5222_;
        }
        11 => {
            let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
            v___x_5223_ = lean_unsigned_to_nat(11);
            return v___x_5223_;
        }
        _ => {
            let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
            v___x_5224_ = lean_unsigned_to_nat(12);
            return v___x_5224_;
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_ctorIdx___boxed(mut v_x_5225_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5226_: *mut LeanObject = core::ptr::null_mut();
    v_res_5226_ = l_Lean_IR_FnBody_ctorIdx(v_x_5225_);
    lean_dec(v_x_5225_);
    return v_res_5226_;
}
pub unsafe fn l_Lean_IR_FnBody_ctorElim___redArg(
    mut v_t_5227_: *mut LeanObject,
    mut v_k_5228_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_5227_) {
        0 => {
            let mut v_x_5229_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ty_5230_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_5231_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_5232_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
            v_x_5229_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5229_);
            v_ty_5230_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_ty_5230_);
            v_e_5231_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc_ref(v_e_5231_);
            v_b_5232_ = lean_ctor_get(v_t_5227_, 3);
            lean_inc(v_b_5232_);
            lean_dec_ref_known(v_t_5227_, 4);
            v___x_5233_ = lean_apply_4(v_k_5228_, v_x_5229_, v_ty_5230_, v_e_5231_, v_b_5232_);
            return v___x_5233_;
        }
        1 => {
            let mut v_j_5234_: *mut LeanObject = core::ptr::null_mut();
            let mut v_xs_5235_: *mut LeanObject = core::ptr::null_mut();
            let mut v_v_5236_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_5237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
            v_j_5234_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_j_5234_);
            v_xs_5235_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc_ref(v_xs_5235_);
            v_v_5236_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc(v_v_5236_);
            v_b_5237_ = lean_ctor_get(v_t_5227_, 3);
            lean_inc(v_b_5237_);
            lean_dec_ref_known(v_t_5227_, 4);
            v___x_5238_ = lean_apply_4(v_k_5228_, v_j_5234_, v_xs_5235_, v_v_5236_, v_b_5237_);
            return v___x_5238_;
        }
        3 => {
            let mut v_x_5239_: *mut LeanObject = core::ptr::null_mut();
            let mut v_cidx_5240_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_5241_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
            v_x_5239_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5239_);
            v_cidx_5240_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_cidx_5240_);
            v_b_5241_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc(v_b_5241_);
            lean_dec_ref_known(v_t_5227_, 3);
            v___x_5242_ = lean_apply_3(v_k_5228_, v_x_5239_, v_cidx_5240_, v_b_5241_);
            return v___x_5242_;
        }
        5 => {
            let mut v_x_5243_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_5244_: *mut LeanObject = core::ptr::null_mut();
            let mut v_offset_5245_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5246_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ty_5247_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_5248_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
            v_x_5243_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5243_);
            v_i_5244_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_i_5244_);
            v_offset_5245_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc(v_offset_5245_);
            v_y_5246_ = lean_ctor_get(v_t_5227_, 3);
            lean_inc(v_y_5246_);
            v_ty_5247_ = lean_ctor_get(v_t_5227_, 4);
            lean_inc(v_ty_5247_);
            v_b_5248_ = lean_ctor_get(v_t_5227_, 5);
            lean_inc(v_b_5248_);
            lean_dec_ref_known(v_t_5227_, 6);
            v___x_5249_ = lean_apply_6(
                v_k_5228_,
                v_x_5243_,
                v_i_5244_,
                v_offset_5245_,
                v_y_5246_,
                v_ty_5247_,
                v_b_5248_,
            );
            return v___x_5249_;
        }
        6 => {
            let mut v_x_5250_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_5251_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_5252_: u8 = 0;
            let mut v_persistent_5253_: u8 = 0;
            let mut v_b_5254_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
            v_x_5250_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5250_);
            v_n_5251_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_n_5251_);
            v_c_5252_ = lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_persistent_5253_ = lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
            );
            v_b_5254_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc(v_b_5254_);
            lean_dec_ref_known(v_t_5227_, 3);
            v___x_5255_ = lean_box((v_c_5252_) as usize);
            v___x_5256_ = lean_box((v_persistent_5253_) as usize);
            v___x_5257_ = lean_apply_5(
                v_k_5228_,
                v_x_5250_,
                v_n_5251_,
                v___x_5255_,
                v___x_5256_,
                v_b_5254_,
            );
            return v___x_5257_;
        }
        7 => {
            let mut v_x_5258_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_5259_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_5260_: u8 = 0;
            let mut v_persistent_5261_: u8 = 0;
            let mut v_b_5262_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
            v_x_5258_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5258_);
            v_n_5259_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_n_5259_);
            v_c_5260_ = lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            );
            v_persistent_5261_ = lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
            );
            v_b_5262_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc(v_b_5262_);
            lean_dec_ref_known(v_t_5227_, 3);
            v___x_5263_ = lean_box((v_c_5260_) as usize);
            v___x_5264_ = lean_box((v_persistent_5261_) as usize);
            v___x_5265_ = lean_apply_5(
                v_k_5228_,
                v_x_5258_,
                v_n_5259_,
                v___x_5263_,
                v___x_5264_,
                v_b_5262_,
            );
            return v___x_5265_;
        }
        8 => {
            let mut v_x_5266_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_5267_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
            v_x_5266_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5266_);
            v_b_5267_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_b_5267_);
            lean_dec_ref_known(v_t_5227_, 2);
            v___x_5268_ = lean_apply_2(v_k_5228_, v_x_5266_, v_b_5267_);
            return v___x_5268_;
        }
        9 => {
            let mut v_tid_5269_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_5270_: *mut LeanObject = core::ptr::null_mut();
            let mut v_xType_5271_: *mut LeanObject = core::ptr::null_mut();
            let mut v_cs_5272_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
            v_tid_5269_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_tid_5269_);
            v_x_5270_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_x_5270_);
            v_xType_5271_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc(v_xType_5271_);
            v_cs_5272_ = lean_ctor_get(v_t_5227_, 3);
            lean_inc_ref(v_cs_5272_);
            lean_dec_ref_known(v_t_5227_, 4);
            v___x_5273_ =
                lean_apply_4(v_k_5228_, v_tid_5269_, v_x_5270_, v_xType_5271_, v_cs_5272_);
            return v___x_5273_;
        }
        10 => {
            let mut v_x_5274_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
            v_x_5274_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5274_);
            lean_dec_ref_known(v_t_5227_, 1);
            v___x_5275_ = lean_apply_1(v_k_5228_, v_x_5274_);
            return v___x_5275_;
        }
        11 => {
            let mut v_j_5276_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ys_5277_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
            v_j_5276_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_j_5276_);
            v_ys_5277_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc_ref(v_ys_5277_);
            lean_dec_ref_known(v_t_5227_, 2);
            v___x_5278_ = lean_apply_2(v_k_5228_, v_j_5276_, v_ys_5277_);
            return v___x_5278_;
        }
        12 => {
            return v_k_5228_;
        }
        _ => {
            let mut v_x_5279_: *mut LeanObject = core::ptr::null_mut();
            let mut v_i_5280_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_5281_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_5282_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
            v_x_5279_ = lean_ctor_get(v_t_5227_, 0);
            lean_inc(v_x_5279_);
            v_i_5280_ = lean_ctor_get(v_t_5227_, 1);
            lean_inc(v_i_5280_);
            v_y_5281_ = lean_ctor_get(v_t_5227_, 2);
            lean_inc(v_y_5281_);
            v_b_5282_ = lean_ctor_get(v_t_5227_, 3);
            lean_inc(v_b_5282_);
            lean_dec(v_t_5227_);
            v___x_5283_ = lean_apply_4(v_k_5228_, v_x_5279_, v_i_5280_, v_y_5281_, v_b_5282_);
            return v___x_5283_;
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_ctorElim(
    mut v_motive__2_5284_: *mut LeanObject,
    mut v_ctorIdx_5285_: *mut LeanObject,
    mut v_t_5286_: *mut LeanObject,
    mut v_h_5287_: *mut LeanObject,
    mut v_k_5288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    v___x_5289_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5286_, v_k_5288_);
    return v___x_5289_;
}
pub unsafe fn l_Lean_IR_FnBody_ctorElim___boxed(
    mut v_motive__2_5290_: *mut LeanObject,
    mut v_ctorIdx_5291_: *mut LeanObject,
    mut v_t_5292_: *mut LeanObject,
    mut v_h_5293_: *mut LeanObject,
    mut v_k_5294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5295_: *mut LeanObject = core::ptr::null_mut();
    v_res_5295_ = l_Lean_IR_FnBody_ctorElim(
        v_motive__2_5290_,
        v_ctorIdx_5291_,
        v_t_5292_,
        v_h_5293_,
        v_k_5294_,
    );
    lean_dec(v_ctorIdx_5291_);
    return v_res_5295_;
}
pub unsafe fn l_Lean_IR_FnBody_vdecl_elim___redArg(
    mut v_t_5296_: *mut LeanObject,
    mut v_vdecl_5297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    v___x_5298_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5296_, v_vdecl_5297_);
    return v___x_5298_;
}
pub unsafe fn l_Lean_IR_FnBody_vdecl_elim(
    mut v_motive__2_5299_: *mut LeanObject,
    mut v_t_5300_: *mut LeanObject,
    mut v_h_5301_: *mut LeanObject,
    mut v_vdecl_5302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    v___x_5303_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5300_, v_vdecl_5302_);
    return v___x_5303_;
}
pub unsafe fn l_Lean_IR_FnBody_jdecl_elim___redArg(
    mut v_t_5304_: *mut LeanObject,
    mut v_jdecl_5305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    v___x_5306_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5304_, v_jdecl_5305_);
    return v___x_5306_;
}
pub unsafe fn l_Lean_IR_FnBody_jdecl_elim(
    mut v_motive__2_5307_: *mut LeanObject,
    mut v_t_5308_: *mut LeanObject,
    mut v_h_5309_: *mut LeanObject,
    mut v_jdecl_5310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    v___x_5311_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5308_, v_jdecl_5310_);
    return v___x_5311_;
}
pub unsafe fn l_Lean_IR_FnBody_set_elim___redArg(
    mut v_t_5312_: *mut LeanObject,
    mut v_set_5313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    v___x_5314_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5312_, v_set_5313_);
    return v___x_5314_;
}
pub unsafe fn l_Lean_IR_FnBody_set_elim(
    mut v_motive__2_5315_: *mut LeanObject,
    mut v_t_5316_: *mut LeanObject,
    mut v_h_5317_: *mut LeanObject,
    mut v_set_5318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    v___x_5319_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5316_, v_set_5318_);
    return v___x_5319_;
}
pub unsafe fn l_Lean_IR_FnBody_setTag_elim___redArg(
    mut v_t_5320_: *mut LeanObject,
    mut v_setTag_5321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    v___x_5322_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5320_, v_setTag_5321_);
    return v___x_5322_;
}
pub unsafe fn l_Lean_IR_FnBody_setTag_elim(
    mut v_motive__2_5323_: *mut LeanObject,
    mut v_t_5324_: *mut LeanObject,
    mut v_h_5325_: *mut LeanObject,
    mut v_setTag_5326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    v___x_5327_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5324_, v_setTag_5326_);
    return v___x_5327_;
}
pub unsafe fn l_Lean_IR_FnBody_uset_elim___redArg(
    mut v_t_5328_: *mut LeanObject,
    mut v_uset_5329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    v___x_5330_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5328_, v_uset_5329_);
    return v___x_5330_;
}
pub unsafe fn l_Lean_IR_FnBody_uset_elim(
    mut v_motive__2_5331_: *mut LeanObject,
    mut v_t_5332_: *mut LeanObject,
    mut v_h_5333_: *mut LeanObject,
    mut v_uset_5334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5335_: *mut LeanObject = core::ptr::null_mut();
    v___x_5335_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5332_, v_uset_5334_);
    return v___x_5335_;
}
pub unsafe fn l_Lean_IR_FnBody_sset_elim___redArg(
    mut v_t_5336_: *mut LeanObject,
    mut v_sset_5337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    v___x_5338_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5336_, v_sset_5337_);
    return v___x_5338_;
}
pub unsafe fn l_Lean_IR_FnBody_sset_elim(
    mut v_motive__2_5339_: *mut LeanObject,
    mut v_t_5340_: *mut LeanObject,
    mut v_h_5341_: *mut LeanObject,
    mut v_sset_5342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    v___x_5343_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5340_, v_sset_5342_);
    return v___x_5343_;
}
pub unsafe fn l_Lean_IR_FnBody_inc_elim___redArg(
    mut v_t_5344_: *mut LeanObject,
    mut v_inc_5345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    v___x_5346_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5344_, v_inc_5345_);
    return v___x_5346_;
}
pub unsafe fn l_Lean_IR_FnBody_inc_elim(
    mut v_motive__2_5347_: *mut LeanObject,
    mut v_t_5348_: *mut LeanObject,
    mut v_h_5349_: *mut LeanObject,
    mut v_inc_5350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    v___x_5351_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5348_, v_inc_5350_);
    return v___x_5351_;
}
pub unsafe fn l_Lean_IR_FnBody_dec_elim___redArg(
    mut v_t_5352_: *mut LeanObject,
    mut v_dec_5353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    v___x_5354_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5352_, v_dec_5353_);
    return v___x_5354_;
}
pub unsafe fn l_Lean_IR_FnBody_dec_elim(
    mut v_motive__2_5355_: *mut LeanObject,
    mut v_t_5356_: *mut LeanObject,
    mut v_h_5357_: *mut LeanObject,
    mut v_dec_5358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    v___x_5359_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5356_, v_dec_5358_);
    return v___x_5359_;
}
pub unsafe fn l_Lean_IR_FnBody_del_elim___redArg(
    mut v_t_5360_: *mut LeanObject,
    mut v_del_5361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    v___x_5362_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5360_, v_del_5361_);
    return v___x_5362_;
}
pub unsafe fn l_Lean_IR_FnBody_del_elim(
    mut v_motive__2_5363_: *mut LeanObject,
    mut v_t_5364_: *mut LeanObject,
    mut v_h_5365_: *mut LeanObject,
    mut v_del_5366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    v___x_5367_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5364_, v_del_5366_);
    return v___x_5367_;
}
pub unsafe fn l_Lean_IR_FnBody_case_elim___redArg(
    mut v_t_5368_: *mut LeanObject,
    mut v_case_5369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    v___x_5370_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5368_, v_case_5369_);
    return v___x_5370_;
}
pub unsafe fn l_Lean_IR_FnBody_case_elim(
    mut v_motive__2_5371_: *mut LeanObject,
    mut v_t_5372_: *mut LeanObject,
    mut v_h_5373_: *mut LeanObject,
    mut v_case_5374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    v___x_5375_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5372_, v_case_5374_);
    return v___x_5375_;
}
pub unsafe fn l_Lean_IR_FnBody_ret_elim___redArg(
    mut v_t_5376_: *mut LeanObject,
    mut v_ret_5377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    v___x_5378_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5376_, v_ret_5377_);
    return v___x_5378_;
}
pub unsafe fn l_Lean_IR_FnBody_ret_elim(
    mut v_motive__2_5379_: *mut LeanObject,
    mut v_t_5380_: *mut LeanObject,
    mut v_h_5381_: *mut LeanObject,
    mut v_ret_5382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    v___x_5383_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5380_, v_ret_5382_);
    return v___x_5383_;
}
pub unsafe fn l_Lean_IR_FnBody_jmp_elim___redArg(
    mut v_t_5384_: *mut LeanObject,
    mut v_jmp_5385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    v___x_5386_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5384_, v_jmp_5385_);
    return v___x_5386_;
}
pub unsafe fn l_Lean_IR_FnBody_jmp_elim(
    mut v_motive__2_5387_: *mut LeanObject,
    mut v_t_5388_: *mut LeanObject,
    mut v_h_5389_: *mut LeanObject,
    mut v_jmp_5390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    v___x_5391_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5388_, v_jmp_5390_);
    return v___x_5391_;
}
pub unsafe fn l_Lean_IR_FnBody_unreachable_elim___redArg(
    mut v_t_5392_: *mut LeanObject,
    mut v_unreachable_5393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5392_, v_unreachable_5393_);
    return v___x_5394_;
}
pub unsafe fn l_Lean_IR_FnBody_unreachable_elim(
    mut v_motive__2_5395_: *mut LeanObject,
    mut v_t_5396_: *mut LeanObject,
    mut v_h_5397_: *mut LeanObject,
    mut v_unreachable_5398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5396_, v_unreachable_5398_);
    return v___x_5399_;
}
pub unsafe fn _init_l_Lean_IR_FnBody_nil() -> *mut LeanObject {
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    v___x_5414_ = lean_box(12);
    return v___x_5414_;
}
pub unsafe fn l_Lean_IR_FnBody_isTerminal(mut v_x_5415_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_x_5415_) {
        9 => {
            let mut v___x_5416_: u8 = 0;
            v___x_5416_ = 1;
            return v___x_5416_;
        }
        10 => {
            let mut v___x_5417_: u8 = 0;
            v___x_5417_ = 1;
            return v___x_5417_;
        }
        11 => {
            let mut v___x_5418_: u8 = 0;
            v___x_5418_ = 1;
            return v___x_5418_;
        }
        12 => {
            let mut v___x_5419_: u8 = 0;
            v___x_5419_ = 1;
            return v___x_5419_;
        }
        _ => {
            let mut v___x_5420_: u8 = 0;
            v___x_5420_ = 0;
            return v___x_5420_;
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_isTerminal___boxed(
    mut v_x_5421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5422_: u8 = 0;
    let mut v_r_5423_: *mut LeanObject = core::ptr::null_mut();
    v_res_5422_ = l_Lean_IR_FnBody_isTerminal(v_x_5421_);
    lean_dec(v_x_5421_);
    v_r_5423_ = lean_box((v_res_5422_) as usize);
    return v_r_5423_;
}
pub unsafe fn l_Lean_IR_FnBody_body(mut v_x_5424_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_5424_) {
        0 => {
            let mut v_b_5425_: *mut LeanObject = core::ptr::null_mut();
            v_b_5425_ = lean_ctor_get(v_x_5424_, 3);
            lean_inc(v_b_5425_);
            return v_b_5425_;
        }
        1 => {
            let mut v_b_5426_: *mut LeanObject = core::ptr::null_mut();
            v_b_5426_ = lean_ctor_get(v_x_5424_, 3);
            lean_inc(v_b_5426_);
            return v_b_5426_;
        }
        2 => {
            let mut v_b_5427_: *mut LeanObject = core::ptr::null_mut();
            v_b_5427_ = lean_ctor_get(v_x_5424_, 3);
            lean_inc(v_b_5427_);
            return v_b_5427_;
        }
        4 => {
            let mut v_b_5428_: *mut LeanObject = core::ptr::null_mut();
            v_b_5428_ = lean_ctor_get(v_x_5424_, 3);
            lean_inc(v_b_5428_);
            return v_b_5428_;
        }
        5 => {
            let mut v_b_5429_: *mut LeanObject = core::ptr::null_mut();
            v_b_5429_ = lean_ctor_get(v_x_5424_, 5);
            lean_inc(v_b_5429_);
            return v_b_5429_;
        }
        3 => {
            let mut v_b_5430_: *mut LeanObject = core::ptr::null_mut();
            v_b_5430_ = lean_ctor_get(v_x_5424_, 2);
            lean_inc(v_b_5430_);
            return v_b_5430_;
        }
        6 => {
            let mut v_b_5431_: *mut LeanObject = core::ptr::null_mut();
            v_b_5431_ = lean_ctor_get(v_x_5424_, 2);
            lean_inc(v_b_5431_);
            return v_b_5431_;
        }
        7 => {
            let mut v_b_5432_: *mut LeanObject = core::ptr::null_mut();
            v_b_5432_ = lean_ctor_get(v_x_5424_, 2);
            lean_inc(v_b_5432_);
            return v_b_5432_;
        }
        8 => {
            let mut v_b_5433_: *mut LeanObject = core::ptr::null_mut();
            v_b_5433_ = lean_ctor_get(v_x_5424_, 1);
            lean_inc(v_b_5433_);
            return v_b_5433_;
        }
        _ => {
            lean_inc(v_x_5424_);
            return v_x_5424_;
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_body___boxed(mut v_x_5434_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5435_: *mut LeanObject = core::ptr::null_mut();
    v_res_5435_ = l_Lean_IR_FnBody_body(v_x_5434_);
    lean_dec(v_x_5434_);
    return v_res_5435_;
}
pub unsafe fn l_Lean_IR_FnBody_setBody(
    mut v_x_5436_: *mut LeanObject,
    mut v_x_5437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5447_: u8 = 0;
    let mut v_unused_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_unused_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5465_: u8 = 0;
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v_unused_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5476_: u8 = 0;
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5480_: u8 = 0;
    let mut v_unused_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5489_: u8 = 0;
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut v_unused_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5499_: u8 = 0;
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5503_: u8 = 0;
    let mut v_unused_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5507_: u8 = 0;
    let mut v_persistent_5508_: u8 = 0;
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5511_: u8 = 0;
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5515_: u8 = 0;
    let mut v_unused_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5519_: u8 = 0;
    let mut v_persistent_5520_: u8 = 0;
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5523_: u8 = 0;
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5527_: u8 = 0;
    let mut v_unused_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_unused_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_5436_) {
                0 => {
                    v_x_5438_ = lean_ctor_get(v_x_5436_, 0);
                    v_ty_5439_ = lean_ctor_get(v_x_5436_, 1);
                    v_e_5440_ = lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5447_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5447_ == 0 {
                        v_unused_5448_ = lean_ctor_get(v_x_5436_, 3);
                        lean_dec(v_unused_5448_);
                        v___x_5442_ = v_x_5436_;
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_e_5440_);
                        lean_inc(v_ty_5439_);
                        lean_inc(v_x_5438_);
                        lean_dec(v_x_5436_);
                        v___x_5442_ = lean_box(0);
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_j_5449_ = lean_ctor_get(v_x_5436_, 0);
                    v_xs_5450_ = lean_ctor_get(v_x_5436_, 1);
                    v_v_5451_ = lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5458_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5458_ == 0 {
                        v_unused_5459_ = lean_ctor_get(v_x_5436_, 3);
                        lean_dec(v_unused_5459_);
                        v___x_5453_ = v_x_5436_;
                        v_isShared_5454_ = v_isSharedCheck_5458_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_v_5451_);
                        lean_inc(v_xs_5450_);
                        lean_inc(v_j_5449_);
                        lean_dec(v_x_5436_);
                        v___x_5453_ = lean_box(0);
                        v_isShared_5454_ = v_isSharedCheck_5458_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_x_5460_ = lean_ctor_get(v_x_5436_, 0);
                    v_i_5461_ = lean_ctor_get(v_x_5436_, 1);
                    v_y_5462_ = lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5469_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5469_ == 0 {
                        v_unused_5470_ = lean_ctor_get(v_x_5436_, 3);
                        lean_dec(v_unused_5470_);
                        v___x_5464_ = v_x_5436_;
                        v_isShared_5465_ = v_isSharedCheck_5469_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_y_5462_);
                        lean_inc(v_i_5461_);
                        lean_inc(v_x_5460_);
                        lean_dec(v_x_5436_);
                        v___x_5464_ = lean_box(0);
                        v_isShared_5465_ = v_isSharedCheck_5469_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_x_5471_ = lean_ctor_get(v_x_5436_, 0);
                    v_i_5472_ = lean_ctor_get(v_x_5436_, 1);
                    v_y_5473_ = lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5480_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5480_ == 0 {
                        v_unused_5481_ = lean_ctor_get(v_x_5436_, 3);
                        lean_dec(v_unused_5481_);
                        v___x_5475_ = v_x_5436_;
                        v_isShared_5476_ = v_isSharedCheck_5480_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_y_5473_);
                        lean_inc(v_i_5472_);
                        lean_inc(v_x_5471_);
                        lean_dec(v_x_5436_);
                        v___x_5475_ = lean_box(0);
                        v_isShared_5476_ = v_isSharedCheck_5480_;
                        state = 7;
                        continue;
                    }
                }
                5 => {
                    v_x_5482_ = lean_ctor_get(v_x_5436_, 0);
                    v_i_5483_ = lean_ctor_get(v_x_5436_, 1);
                    v_offset_5484_ = lean_ctor_get(v_x_5436_, 2);
                    v_y_5485_ = lean_ctor_get(v_x_5436_, 3);
                    v_ty_5486_ = lean_ctor_get(v_x_5436_, 4);
                    v_isSharedCheck_5493_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5493_ == 0 {
                        v_unused_5494_ = lean_ctor_get(v_x_5436_, 5);
                        lean_dec(v_unused_5494_);
                        v___x_5488_ = v_x_5436_;
                        v_isShared_5489_ = v_isSharedCheck_5493_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_ty_5486_);
                        lean_inc(v_y_5485_);
                        lean_inc(v_offset_5484_);
                        lean_inc(v_i_5483_);
                        lean_inc(v_x_5482_);
                        lean_dec(v_x_5436_);
                        v___x_5488_ = lean_box(0);
                        v_isShared_5489_ = v_isSharedCheck_5493_;
                        state = 9;
                        continue;
                    }
                }
                3 => {
                    v_x_5495_ = lean_ctor_get(v_x_5436_, 0);
                    v_cidx_5496_ = lean_ctor_get(v_x_5436_, 1);
                    v_isSharedCheck_5503_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5503_ == 0 {
                        v_unused_5504_ = lean_ctor_get(v_x_5436_, 2);
                        lean_dec(v_unused_5504_);
                        v___x_5498_ = v_x_5436_;
                        v_isShared_5499_ = v_isSharedCheck_5503_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_cidx_5496_);
                        lean_inc(v_x_5495_);
                        lean_dec(v_x_5436_);
                        v___x_5498_ = lean_box(0);
                        v_isShared_5499_ = v_isSharedCheck_5503_;
                        state = 11;
                        continue;
                    }
                }
                6 => {
                    v_x_5505_ = lean_ctor_get(v_x_5436_, 0);
                    v_n_5506_ = lean_ctor_get(v_x_5436_, 1);
                    v_c_5507_ = lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_5508_ = lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isSharedCheck_5515_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5515_ == 0 {
                        v_unused_5516_ = lean_ctor_get(v_x_5436_, 2);
                        lean_dec(v_unused_5516_);
                        v___x_5510_ = v_x_5436_;
                        v_isShared_5511_ = v_isSharedCheck_5515_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_n_5506_);
                        lean_inc(v_x_5505_);
                        lean_dec(v_x_5436_);
                        v___x_5510_ = lean_box(0);
                        v_isShared_5511_ = v_isSharedCheck_5515_;
                        state = 13;
                        continue;
                    }
                }
                7 => {
                    v_x_5517_ = lean_ctor_get(v_x_5436_, 0);
                    v_n_5518_ = lean_ctor_get(v_x_5436_, 1);
                    v_c_5519_ = lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_persistent_5520_ = lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                    );
                    v_isSharedCheck_5527_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5527_ == 0 {
                        v_unused_5528_ = lean_ctor_get(v_x_5436_, 2);
                        lean_dec(v_unused_5528_);
                        v___x_5522_ = v_x_5436_;
                        v_isShared_5523_ = v_isSharedCheck_5527_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_n_5518_);
                        lean_inc(v_x_5517_);
                        lean_dec(v_x_5436_);
                        v___x_5522_ = lean_box(0);
                        v_isShared_5523_ = v_isSharedCheck_5527_;
                        state = 15;
                        continue;
                    }
                }
                8 => {
                    v_x_5529_ = lean_ctor_get(v_x_5436_, 0);
                    v_isSharedCheck_5536_ = (!lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5536_ == 0 {
                        v_unused_5537_ = lean_ctor_get(v_x_5436_, 1);
                        lean_dec(v_unused_5537_);
                        v___x_5531_ = v_x_5436_;
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_x_5529_);
                        lean_dec(v_x_5436_);
                        v___x_5531_ = lean_box(0);
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 17;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_x_5437_);
                    return v_x_5436_;
                }
            },
            1 => {
                if v_isShared_5443_ == 0 {
                    lean_ctor_set(v___x_5442_, 3, v_x_5437_);
                    v___x_5445_ = v___x_5442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_x_5438_);
                    lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_ty_5439_);
                    lean_ctor_set(v_reuseFailAlloc_5446_, 2, v_e_5440_);
                    lean_ctor_set(v_reuseFailAlloc_5446_, 3, v_x_5437_);
                    v___x_5445_ = v_reuseFailAlloc_5446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5445_;
            }
            3 => {
                if v_isShared_5454_ == 0 {
                    lean_ctor_set(v___x_5453_, 3, v_x_5437_);
                    v___x_5456_ = v___x_5453_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5457_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_j_5449_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_xs_5450_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 2, v_v_5451_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 3, v_x_5437_);
                    v___x_5456_ = v_reuseFailAlloc_5457_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5456_;
            }
            5 => {
                if v_isShared_5465_ == 0 {
                    lean_ctor_set(v___x_5464_, 3, v_x_5437_);
                    v___x_5467_ = v___x_5464_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5468_ = lean_alloc_ctor(2, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_x_5460_);
                    lean_ctor_set(v_reuseFailAlloc_5468_, 1, v_i_5461_);
                    lean_ctor_set(v_reuseFailAlloc_5468_, 2, v_y_5462_);
                    lean_ctor_set(v_reuseFailAlloc_5468_, 3, v_x_5437_);
                    v___x_5467_ = v_reuseFailAlloc_5468_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5467_;
            }
            7 => {
                if v_isShared_5476_ == 0 {
                    lean_ctor_set(v___x_5475_, 3, v_x_5437_);
                    v___x_5478_ = v___x_5475_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5479_ = lean_alloc_ctor(4, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_x_5471_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 1, v_i_5472_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 2, v_y_5473_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 3, v_x_5437_);
                    v___x_5478_ = v_reuseFailAlloc_5479_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5478_;
            }
            9 => {
                if v_isShared_5489_ == 0 {
                    lean_ctor_set(v___x_5488_, 5, v_x_5437_);
                    v___x_5491_ = v___x_5488_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = lean_alloc_ctor(5, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_x_5482_);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 1, v_i_5483_);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 2, v_offset_5484_);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 3, v_y_5485_);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 4, v_ty_5486_);
                    lean_ctor_set(v_reuseFailAlloc_5492_, 5, v_x_5437_);
                    v___x_5491_ = v_reuseFailAlloc_5492_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5491_;
            }
            11 => {
                if v_isShared_5499_ == 0 {
                    lean_ctor_set(v___x_5498_, 2, v_x_5437_);
                    v___x_5501_ = v___x_5498_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5502_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_x_5495_);
                    lean_ctor_set(v_reuseFailAlloc_5502_, 1, v_cidx_5496_);
                    lean_ctor_set(v_reuseFailAlloc_5502_, 2, v_x_5437_);
                    v___x_5501_ = v_reuseFailAlloc_5502_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5501_;
            }
            13 => {
                if v_isShared_5511_ == 0 {
                    lean_ctor_set(v___x_5510_, 2, v_x_5437_);
                    v___x_5513_ = v___x_5510_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5514_ = lean_alloc_ctor(6, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_x_5505_);
                    lean_ctor_set(v_reuseFailAlloc_5514_, 1, v_n_5506_);
                    lean_ctor_set(v_reuseFailAlloc_5514_, 2, v_x_5437_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5514_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_c_5507_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5514_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_5508_,
                    );
                    v___x_5513_ = v_reuseFailAlloc_5514_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5513_;
            }
            15 => {
                if v_isShared_5523_ == 0 {
                    lean_ctor_set(v___x_5522_, 2, v_x_5437_);
                    v___x_5525_ = v___x_5522_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5526_ = lean_alloc_ctor(7, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_x_5517_);
                    lean_ctor_set(v_reuseFailAlloc_5526_, 1, v_n_5518_);
                    lean_ctor_set(v_reuseFailAlloc_5526_, 2, v_x_5437_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5526_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_c_5519_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5526_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_persistent_5520_,
                    );
                    v___x_5525_ = v_reuseFailAlloc_5526_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5525_;
            }
            17 => {
                if v_isShared_5532_ == 0 {
                    lean_ctor_set(v___x_5531_, 1, v_x_5437_);
                    v___x_5534_ = v___x_5531_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_x_5529_);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_x_5437_);
                    v___x_5534_ = v_reuseFailAlloc_5535_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_resetBody(mut v_b_5538_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    v___x_5539_ = lean_box(12);
    v___x_5540_ = l_Lean_IR_FnBody_setBody(v_b_5538_, v___x_5539_);
    return v___x_5540_;
}
pub unsafe fn l_Lean_IR_FnBody_split(mut v_b_5541_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_b_5541_) {
                0 => {
                    v_b_5547_ = lean_ctor_get(v_b_5541_, 3);
                    lean_inc(v_b_5547_);
                    v___y_5543_ = v_b_5547_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_b_5548_ = lean_ctor_get(v_b_5541_, 3);
                    lean_inc(v_b_5548_);
                    v___y_5543_ = v_b_5548_;
                    state = 1;
                    continue;
                }
                2 => {
                    v_b_5549_ = lean_ctor_get(v_b_5541_, 3);
                    lean_inc(v_b_5549_);
                    v___y_5543_ = v_b_5549_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_b_5550_ = lean_ctor_get(v_b_5541_, 3);
                    lean_inc(v_b_5550_);
                    v___y_5543_ = v_b_5550_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_b_5551_ = lean_ctor_get(v_b_5541_, 5);
                    lean_inc(v_b_5551_);
                    v___y_5543_ = v_b_5551_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_b_5552_ = lean_ctor_get(v_b_5541_, 2);
                    lean_inc(v_b_5552_);
                    v___y_5543_ = v_b_5552_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_b_5553_ = lean_ctor_get(v_b_5541_, 2);
                    lean_inc(v_b_5553_);
                    v___y_5543_ = v_b_5553_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_b_5554_ = lean_ctor_get(v_b_5541_, 2);
                    lean_inc(v_b_5554_);
                    v___y_5543_ = v_b_5554_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_b_5555_ = lean_ctor_get(v_b_5541_, 1);
                    lean_inc(v_b_5555_);
                    v___y_5543_ = v_b_5555_;
                    state = 1;
                    continue;
                }
                _ => {
                    lean_inc(v_b_5541_);
                    v___y_5543_ = v_b_5541_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_5544_ = lean_box(12);
                v_c_5545_ = l_Lean_IR_FnBody_setBody(v_b_5541_, v___x_5544_);
                v___x_5546_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5546_, 0, v_c_5545_);
                lean_ctor_set(v___x_5546_, 1, v___y_5543_);
                return v___x_5546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Alt_body(mut v_x_5556_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_5556_) == 0 {
        let mut v_b_5557_: *mut LeanObject = core::ptr::null_mut();
        v_b_5557_ = lean_ctor_get(v_x_5556_, 1);
        lean_inc(v_b_5557_);
        return v_b_5557_;
    } else {
        let mut v_b_5558_: *mut LeanObject = core::ptr::null_mut();
        v_b_5558_ = lean_ctor_get(v_x_5556_, 0);
        lean_inc(v_b_5558_);
        return v_b_5558_;
    }
}
pub unsafe fn l_Lean_IR_Alt_body___boxed(mut v_x_5559_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5560_: *mut LeanObject = core::ptr::null_mut();
    v_res_5560_ = l_Lean_IR_Alt_body(v_x_5559_);
    lean_dec_ref(v_x_5559_);
    return v_res_5560_;
}
pub unsafe fn l_Lean_IR_Alt_setBody(
    mut v_x_5561_: *mut LeanObject,
    mut v_x_5562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut v_unused_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_unused_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5561_) == 0 {
                    v_info_5563_ = lean_ctor_get(v_x_5561_, 0);
                    v_isSharedCheck_5570_ = (!lean_is_exclusive(v_x_5561_)) as u8;
                    if v_isSharedCheck_5570_ == 0 {
                        v_unused_5571_ = lean_ctor_get(v_x_5561_, 1);
                        lean_dec(v_unused_5571_);
                        v___x_5565_ = v_x_5561_;
                        v_isShared_5566_ = v_isSharedCheck_5570_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_info_5563_);
                        lean_dec(v_x_5561_);
                        v___x_5565_ = lean_box(0);
                        v_isShared_5566_ = v_isSharedCheck_5570_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_5578_ = (!lean_is_exclusive(v_x_5561_)) as u8;
                    if v_isSharedCheck_5578_ == 0 {
                        v_unused_5579_ = lean_ctor_get(v_x_5561_, 0);
                        lean_dec(v_unused_5579_);
                        v___x_5573_ = v_x_5561_;
                        v_isShared_5574_ = v_isSharedCheck_5578_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_5561_);
                        v___x_5573_ = lean_box(0);
                        v_isShared_5574_ = v_isSharedCheck_5578_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5566_ == 0 {
                    lean_ctor_set(v___x_5565_, 1, v_x_5562_);
                    v___x_5568_ = v___x_5565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_info_5563_);
                    lean_ctor_set(v_reuseFailAlloc_5569_, 1, v_x_5562_);
                    v___x_5568_ = v_reuseFailAlloc_5569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5568_;
            }
            3 => {
                if v_isShared_5574_ == 0 {
                    lean_ctor_set(v___x_5573_, 0, v_x_5562_);
                    v___x_5576_ = v___x_5573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_x_5562_);
                    v___x_5576_ = v_reuseFailAlloc_5577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Alt_modifyBody(
    mut v_f_5580_: *mut LeanObject,
    mut v_x_5581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5591_: u8 = 0;
    let mut v_b_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5581_) == 0 {
                    v_info_5582_ = lean_ctor_get(v_x_5581_, 0);
                    v_b_5583_ = lean_ctor_get(v_x_5581_, 1);
                    v_isSharedCheck_5591_ = (!lean_is_exclusive(v_x_5581_)) as u8;
                    if v_isSharedCheck_5591_ == 0 {
                        v___x_5585_ = v_x_5581_;
                        v_isShared_5586_ = v_isSharedCheck_5591_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_b_5583_);
                        lean_inc(v_info_5582_);
                        lean_dec(v_x_5581_);
                        v___x_5585_ = lean_box(0);
                        v_isShared_5586_ = v_isSharedCheck_5591_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_b_5592_ = lean_ctor_get(v_x_5581_, 0);
                    v_isSharedCheck_5600_ = (!lean_is_exclusive(v_x_5581_)) as u8;
                    if v_isSharedCheck_5600_ == 0 {
                        v___x_5594_ = v_x_5581_;
                        v_isShared_5595_ = v_isSharedCheck_5600_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_b_5592_);
                        lean_dec(v_x_5581_);
                        v___x_5594_ = lean_box(0);
                        v_isShared_5595_ = v_isSharedCheck_5600_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5587_ = lean_apply_1(v_f_5580_, v_b_5583_);
                if v_isShared_5586_ == 0 {
                    lean_ctor_set(v___x_5585_, 1, v___x_5587_);
                    v___x_5589_ = v___x_5585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_info_5582_);
                    lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5587_);
                    v___x_5589_ = v_reuseFailAlloc_5590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5589_;
            }
            3 => {
                v___x_5596_ = lean_apply_1(v_f_5580_, v_b_5592_);
                if v_isShared_5595_ == 0 {
                    lean_ctor_set(v___x_5594_, 0, v___x_5596_);
                    v___x_5598_ = v___x_5594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5596_);
                    v___x_5598_ = v_reuseFailAlloc_5599_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Alt_modifyBodyM___redArg___lam__0(
    mut v_info_5601_: *mut LeanObject,
    mut v_b_5602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    v___x_5603_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5603_, 0, v_info_5601_);
    lean_ctor_set(v___x_5603_, 1, v_b_5602_);
    return v___x_5603_;
}
pub unsafe fn l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(
    mut v_b_5604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    v___x_5605_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5605_, 0, v_b_5604_);
    return v___x_5605_;
}
pub unsafe fn l_Lean_IR_Alt_modifyBodyM___redArg(
    mut v_inst_5607_: *mut LeanObject,
    mut v_f_5608_: *mut LeanObject,
    mut v_x_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5610_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5610_ = lean_ctor_get(v_inst_5607_, 0);
    lean_inc_ref(v_toApplicative_5610_);
    lean_dec_ref(v_inst_5607_);
    if lean_obj_tag(v_x_5609_) == 0 {
        let mut v_toFunctor_5611_: *mut LeanObject = core::ptr::null_mut();
        let mut v_info_5612_: *mut LeanObject = core::ptr::null_mut();
        let mut v_b_5613_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_5614_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5615_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_5611_ = lean_ctor_get(v_toApplicative_5610_, 0);
        lean_inc_ref(v_toFunctor_5611_);
        lean_dec_ref(v_toApplicative_5610_);
        v_info_5612_ = lean_ctor_get(v_x_5609_, 0);
        lean_inc_ref(v_info_5612_);
        v_b_5613_ = lean_ctor_get(v_x_5609_, 1);
        lean_inc(v_b_5613_);
        lean_dec_ref_known(v_x_5609_, 2);
        v_map_5614_ = lean_ctor_get(v_toFunctor_5611_, 0);
        lean_inc(v_map_5614_);
        lean_dec_ref(v_toFunctor_5611_);
        v___f_5615_ = lean_alloc_closure(
            l_Lean_IR_Alt_modifyBodyM___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_5615_, 0, v_info_5612_);
        v___x_5616_ = lean_apply_1(v_f_5608_, v_b_5613_);
        v___x_5617_ = lean_apply_4(
            v_map_5614_,
            lean_box(0),
            lean_box(0),
            v___f_5615_,
            v___x_5616_,
        );
        return v___x_5617_;
    } else {
        let mut v_toFunctor_5618_: *mut LeanObject = core::ptr::null_mut();
        let mut v_b_5619_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_5620_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5621_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_5618_ = lean_ctor_get(v_toApplicative_5610_, 0);
        lean_inc_ref(v_toFunctor_5618_);
        lean_dec_ref(v_toApplicative_5610_);
        v_b_5619_ = lean_ctor_get(v_x_5609_, 0);
        lean_inc(v_b_5619_);
        lean_dec_ref_known(v_x_5609_, 1);
        v_map_5620_ = lean_ctor_get(v_toFunctor_5618_, 0);
        lean_inc(v_map_5620_);
        lean_dec_ref(v_toFunctor_5618_);
        v___f_5621_ = l_Lean_IR_Alt_modifyBodyM___redArg___closed__0;
        v___x_5622_ = lean_apply_1(v_f_5608_, v_b_5619_);
        v___x_5623_ = lean_apply_4(
            v_map_5620_,
            lean_box(0),
            lean_box(0),
            v___f_5621_,
            v___x_5622_,
        );
        return v___x_5623_;
    }
}
pub unsafe fn l_Lean_IR_Alt_modifyBodyM(
    mut v_m_5624_: *mut LeanObject,
    mut v_inst_5625_: *mut LeanObject,
    mut v_f_5626_: *mut LeanObject,
    mut v_x_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5628_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5628_ = lean_ctor_get(v_inst_5625_, 0);
    lean_inc_ref(v_toApplicative_5628_);
    lean_dec_ref(v_inst_5625_);
    if lean_obj_tag(v_x_5627_) == 0 {
        let mut v_toFunctor_5629_: *mut LeanObject = core::ptr::null_mut();
        let mut v_info_5630_: *mut LeanObject = core::ptr::null_mut();
        let mut v_b_5631_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_5632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_5629_ = lean_ctor_get(v_toApplicative_5628_, 0);
        lean_inc_ref(v_toFunctor_5629_);
        lean_dec_ref(v_toApplicative_5628_);
        v_info_5630_ = lean_ctor_get(v_x_5627_, 0);
        lean_inc_ref(v_info_5630_);
        v_b_5631_ = lean_ctor_get(v_x_5627_, 1);
        lean_inc(v_b_5631_);
        lean_dec_ref_known(v_x_5627_, 2);
        v_map_5632_ = lean_ctor_get(v_toFunctor_5629_, 0);
        lean_inc(v_map_5632_);
        lean_dec_ref(v_toFunctor_5629_);
        v___f_5633_ = lean_alloc_closure(
            l_Lean_IR_Alt_modifyBodyM___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_5633_, 0, v_info_5630_);
        v___x_5634_ = lean_apply_1(v_f_5626_, v_b_5631_);
        v___x_5635_ = lean_apply_4(
            v_map_5632_,
            lean_box(0),
            lean_box(0),
            v___f_5633_,
            v___x_5634_,
        );
        return v___x_5635_;
    } else {
        let mut v_toFunctor_5636_: *mut LeanObject = core::ptr::null_mut();
        let mut v_b_5637_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_5638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
        v_toFunctor_5636_ = lean_ctor_get(v_toApplicative_5628_, 0);
        lean_inc_ref(v_toFunctor_5636_);
        lean_dec_ref(v_toApplicative_5628_);
        v_b_5637_ = lean_ctor_get(v_x_5627_, 0);
        lean_inc(v_b_5637_);
        lean_dec_ref_known(v_x_5627_, 1);
        v_map_5638_ = lean_ctor_get(v_toFunctor_5636_, 0);
        lean_inc(v_map_5638_);
        lean_dec_ref(v_toFunctor_5636_);
        v___f_5639_ = l_Lean_IR_Alt_modifyBodyM___redArg___closed__0;
        v___x_5640_ = lean_apply_1(v_f_5626_, v_b_5637_);
        v___x_5641_ = lean_apply_4(
            v_map_5638_,
            lean_box(0),
            lean_box(0),
            v___f_5639_,
            v___x_5640_,
        );
        return v___x_5641_;
    }
}
pub unsafe fn l_Lean_IR_Alt_isDefault(mut v_x_5642_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_5642_) == 0 {
        let mut v___x_5643_: u8 = 0;
        v___x_5643_ = 0;
        return v___x_5643_;
    } else {
        let mut v___x_5644_: u8 = 0;
        v___x_5644_ = 1;
        return v___x_5644_;
    }
}
pub unsafe fn l_Lean_IR_Alt_isDefault___boxed(mut v_x_5645_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5646_: u8 = 0;
    let mut v_r_5647_: *mut LeanObject = core::ptr::null_mut();
    v_res_5646_ = l_Lean_IR_Alt_isDefault(v_x_5645_);
    lean_dec_ref(v_x_5645_);
    v_r_5647_ = lean_box((v_res_5646_) as usize);
    return v_r_5647_;
}
pub unsafe fn l_Lean_IR_push(
    mut v_bs_5648_: *mut LeanObject,
    mut v_b_5649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut LeanObject = core::ptr::null_mut();
    v___x_5650_ = lean_box(12);
    v_b_5651_ = l_Lean_IR_FnBody_setBody(v_b_5649_, v___x_5650_);
    v___x_5652_ = lean_array_push(v_bs_5648_, v_b_5651_);
    return v___x_5652_;
}
pub unsafe fn l_Lean_IR_flattenAux(
    mut v_b_5653_: *mut LeanObject,
    mut v_r_5654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: u8 = 0;
    let mut v_b_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5659_ = l_Lean_IR_FnBody_isTerminal(v_b_5653_);
                if v___x_5659_ == 0 {
                    match lean_obj_tag(v_b_5653_) {
                        0 => {
                            v_b_5660_ = lean_ctor_get(v_b_5653_, 3);
                            lean_inc(v_b_5660_);
                            v___y_5656_ = v_b_5660_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_b_5661_ = lean_ctor_get(v_b_5653_, 3);
                            lean_inc(v_b_5661_);
                            v___y_5656_ = v_b_5661_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_b_5662_ = lean_ctor_get(v_b_5653_, 3);
                            lean_inc(v_b_5662_);
                            v___y_5656_ = v_b_5662_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v_b_5663_ = lean_ctor_get(v_b_5653_, 3);
                            lean_inc(v_b_5663_);
                            v___y_5656_ = v_b_5663_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v_b_5664_ = lean_ctor_get(v_b_5653_, 5);
                            lean_inc(v_b_5664_);
                            v___y_5656_ = v_b_5664_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            v_b_5665_ = lean_ctor_get(v_b_5653_, 2);
                            lean_inc(v_b_5665_);
                            v___y_5656_ = v_b_5665_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_b_5666_ = lean_ctor_get(v_b_5653_, 2);
                            lean_inc(v_b_5666_);
                            v___y_5656_ = v_b_5666_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_b_5667_ = lean_ctor_get(v_b_5653_, 2);
                            lean_inc(v_b_5667_);
                            v___y_5656_ = v_b_5667_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_b_5668_ = lean_ctor_get(v_b_5653_, 1);
                            lean_inc(v_b_5668_);
                            v___y_5656_ = v_b_5668_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            lean_inc(v_b_5653_);
                            v___y_5656_ = v_b_5653_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5669_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5669_, 0, v_r_5654_);
                    lean_ctor_set(v___x_5669_, 1, v_b_5653_);
                    return v___x_5669_;
                }
            }
            1 => {
                v___x_5657_ = l_Lean_IR_push(v_r_5654_, v_b_5653_);
                v_b_5653_ = v___y_5656_;
                v_r_5654_ = v___x_5657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_flatten(mut v_b_5672_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    v___x_5673_ = l_Lean_IR_FnBody_flatten___closed__0;
    v___x_5674_ = l_Lean_IR_flattenAux(v_b_5672_, v___x_5673_);
    return v___x_5674_;
}
pub unsafe fn l_panic___at___00Lean_IR_reshapeAux_spec__0(
    mut v___x_5675_: *mut LeanObject,
    mut v_msg_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    v___x_5677_ = lean_panic_fn_borrowed(v___x_5675_, v_msg_5676_);
    return v___x_5677_;
}
pub unsafe fn l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(
    mut v___x_5678_: *mut LeanObject,
    mut v_msg_5679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5680_: *mut LeanObject = core::ptr::null_mut();
    v_res_5680_ = l_panic___at___00Lean_IR_reshapeAux_spec__0(v___x_5678_, v_msg_5679_);
    lean_dec_ref(v___x_5678_);
    return v_res_5680_;
}
pub unsafe fn l_Lean_IR_reshapeAux(
    mut v_a_5685_: *mut LeanObject,
    mut v_i_5686_: *mut LeanObject,
    mut v_b_5687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    let mut v___x_5690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: u8 = 0;
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5688_ = lean_unsigned_to_nat(0);
                v___x_5689_ = lean_nat_dec_eq(v_i_5686_, v___x_5688_);
                if v___x_5689_ == 0 {
                    v___x_5690_ = lean_unsigned_to_nat(1);
                    v_i_5691_ = lean_nat_sub(v_i_5686_, v___x_5690_);
                    lean_dec(v_i_5686_);
                    v___x_5697_ = l_Lean_IR_instInhabitedFnBody_default__1;
                    v___x_5698_ = lean_array_get_size(v_a_5685_);
                    v___x_5699_ = lean_nat_dec_lt(v_i_5691_, v___x_5698_);
                    if v___x_5699_ == 0 {
                        v___x_5700_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5700_, 0, v___x_5697_);
                        lean_ctor_set(v___x_5700_, 1, v_a_5685_);
                        v___x_5701_ = l_Lean_IR_reshapeAux___closed__0;
                        v___x_5702_ = l_Lean_IR_reshapeAux___closed__1;
                        v___x_5703_ = lean_unsigned_to_nat(438);
                        v___x_5704_ = lean_unsigned_to_nat(4);
                        v___x_5705_ = l_Lean_IR_reshapeAux___closed__2;
                        lean_inc(v_i_5691_);
                        v___x_5706_ = l_Nat_reprFast(v_i_5691_);
                        v___x_5707_ = lean_string_append(v___x_5705_, v___x_5706_);
                        lean_dec_ref(v___x_5706_);
                        v___x_5708_ = l_Lean_IR_reshapeAux___closed__3;
                        v___x_5709_ = lean_string_append(v___x_5707_, v___x_5708_);
                        v___x_5710_ = l_mkPanicMessageWithDecl(
                            v___x_5701_,
                            v___x_5702_,
                            v___x_5703_,
                            v___x_5704_,
                            v___x_5709_,
                        );
                        lean_dec_ref(v___x_5709_);
                        v___x_5711_ = lean_panic_fn_borrowed(v___x_5700_, v___x_5710_);
                        lean_dec_ref_known(v___x_5700_, 2);
                        v_fst_5712_ = lean_ctor_get(v___x_5711_, 0);
                        lean_inc(v_fst_5712_);
                        v_snd_5713_ = lean_ctor_get(v___x_5711_, 1);
                        lean_inc(v_snd_5713_);
                        lean_dec(v___x_5711_);
                        v_fst_5693_ = v_fst_5712_;
                        v_snd_5694_ = v_snd_5713_;
                        state = 1;
                        continue;
                    } else {
                        v_e_5714_ = lean_array_fget(v_a_5685_, v_i_5691_);
                        v_xs_x27_5715_ = lean_array_fset(v_a_5685_, v_i_5691_, v___x_5697_);
                        v_fst_5693_ = v_e_5714_;
                        v_snd_5694_ = v_xs_x27_5715_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_i_5686_);
                    lean_dec_ref(v_a_5685_);
                    return v_b_5687_;
                }
            }
            1 => {
                v_b_5695_ = l_Lean_IR_FnBody_setBody(v_fst_5693_, v_b_5687_);
                v_a_5685_ = v_snd_5694_;
                v_i_5686_ = v_i_5691_;
                v_b_5687_ = v_b_5695_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_reshape(
    mut v_bs_5716_: *mut LeanObject,
    mut v_term_5717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut LeanObject = core::ptr::null_mut();
    v___x_5718_ = lean_array_get_size(v_bs_5716_);
    v___x_5719_ = l_Lean_IR_reshapeAux(v_bs_5716_, v___x_5718_, v_term_5717_);
    return v___x_5719_;
}
pub unsafe fn l_Lean_IR_modifyJPs___lam__0(
    mut v_f_5720_: *mut LeanObject,
    mut v_x_5721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_j_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5728_: u8 = 0;
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5721_) == 1 {
                    v_j_5722_ = lean_ctor_get(v_x_5721_, 0);
                    v_xs_5723_ = lean_ctor_get(v_x_5721_, 1);
                    v_v_5724_ = lean_ctor_get(v_x_5721_, 2);
                    v_b_5725_ = lean_ctor_get(v_x_5721_, 3);
                    v_isSharedCheck_5733_ = (!lean_is_exclusive(v_x_5721_)) as u8;
                    if v_isSharedCheck_5733_ == 0 {
                        v___x_5727_ = v_x_5721_;
                        v_isShared_5728_ = v_isSharedCheck_5733_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_b_5725_);
                        lean_inc(v_v_5724_);
                        lean_inc(v_xs_5723_);
                        lean_inc(v_j_5722_);
                        lean_dec(v_x_5721_);
                        v___x_5727_ = lean_box(0);
                        v_isShared_5728_ = v_isSharedCheck_5733_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_5720_);
                    return v_x_5721_;
                }
            }
            1 => {
                v___x_5729_ = lean_apply_1(v_f_5720_, v_v_5724_);
                if v_isShared_5728_ == 0 {
                    lean_ctor_set(v___x_5727_, 2, v___x_5729_);
                    v___x_5731_ = v___x_5727_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5732_ = lean_alloc_ctor(1, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_j_5722_);
                    lean_ctor_set(v_reuseFailAlloc_5732_, 1, v_xs_5723_);
                    lean_ctor_set(v_reuseFailAlloc_5732_, 2, v___x_5729_);
                    lean_ctor_set(v_reuseFailAlloc_5732_, 3, v_b_5725_);
                    v___x_5731_ = v_reuseFailAlloc_5732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_modifyJPs(
    mut v_bs_5753_: *mut LeanObject,
    mut v_f_5754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5757_: usize = 0;
    let mut v___x_5758_: usize = 0;
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    v___f_5755_ = lean_alloc_closure(l_Lean_IR_modifyJPs___lam__0 as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_5755_, 0, v_f_5754_);
    v___x_5756_ = l_Lean_IR_modifyJPs___closed__9;
    v_sz_5757_ = lean_array_size(v_bs_5753_);
    v___x_5758_ = 0usize;
    v___x_5759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_5756_,
        v___f_5755_,
        v_sz_5757_,
        v___x_5758_,
        v_bs_5753_,
    );
    return v___x_5759_;
}
pub unsafe fn l_Lean_IR_modifyJPsM___redArg___lam__0(
    mut v_j_5760_: *mut LeanObject,
    mut v_xs_5761_: *mut LeanObject,
    mut v_b_5762_: *mut LeanObject,
    mut v_toPure_5763_: *mut LeanObject,
    mut v_____do__lift_5764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    v___x_5765_ = lean_alloc_ctor(1, 4, (0) as u32);
    lean_ctor_set(v___x_5765_, 0, v_j_5760_);
    lean_ctor_set(v___x_5765_, 1, v_xs_5761_);
    lean_ctor_set(v___x_5765_, 2, v_____do__lift_5764_);
    lean_ctor_set(v___x_5765_, 3, v_b_5762_);
    v___x_5766_ = lean_apply_2(v_toPure_5763_, lean_box(0), v___x_5765_);
    return v___x_5766_;
}
pub unsafe fn l_Lean_IR_modifyJPsM___redArg___lam__1(
    mut v_toPure_5767_: *mut LeanObject,
    mut v_f_5768_: *mut LeanObject,
    mut v_toBind_5769_: *mut LeanObject,
    mut v_b_5770_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_5770_) == 1 {
        let mut v_j_5771_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_5772_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_5773_: *mut LeanObject = core::ptr::null_mut();
        let mut v_b_5774_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5775_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
        v_j_5771_ = lean_ctor_get(v_b_5770_, 0);
        lean_inc(v_j_5771_);
        v_xs_5772_ = lean_ctor_get(v_b_5770_, 1);
        lean_inc_ref(v_xs_5772_);
        v_v_5773_ = lean_ctor_get(v_b_5770_, 2);
        lean_inc(v_v_5773_);
        v_b_5774_ = lean_ctor_get(v_b_5770_, 3);
        lean_inc(v_b_5774_);
        lean_dec_ref_known(v_b_5770_, 4);
        v___f_5775_ = lean_alloc_closure(
            l_Lean_IR_modifyJPsM___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_5775_, 0, v_j_5771_);
        lean_closure_set(v___f_5775_, 1, v_xs_5772_);
        lean_closure_set(v___f_5775_, 2, v_b_5774_);
        lean_closure_set(v___f_5775_, 3, v_toPure_5767_);
        v___x_5776_ = lean_apply_1(v_f_5768_, v_v_5773_);
        v___x_5777_ = lean_apply_4(
            v_toBind_5769_,
            lean_box(0),
            lean_box(0),
            v___x_5776_,
            v___f_5775_,
        );
        return v___x_5777_;
    } else {
        let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toBind_5769_);
        lean_dec(v_f_5768_);
        v___x_5778_ = lean_apply_2(v_toPure_5767_, lean_box(0), v_b_5770_);
        return v___x_5778_;
    }
}
pub unsafe fn l_Lean_IR_modifyJPsM___redArg(
    mut v_inst_5779_: *mut LeanObject,
    mut v_bs_5780_: *mut LeanObject,
    mut v_f_5781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5786_: usize = 0;
    let mut v___x_5787_: usize = 0;
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5782_ = lean_ctor_get(v_inst_5779_, 0);
    v_toBind_5783_ = lean_ctor_get(v_inst_5779_, 1);
    v_toPure_5784_ = lean_ctor_get(v_toApplicative_5782_, 1);
    lean_inc(v_toBind_5783_);
    lean_inc(v_toPure_5784_);
    v___f_5785_ = lean_alloc_closure(
        l_Lean_IR_modifyJPsM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5785_, 0, v_toPure_5784_);
    lean_closure_set(v___f_5785_, 1, v_f_5781_);
    lean_closure_set(v___f_5785_, 2, v_toBind_5783_);
    v_sz_5786_ = lean_array_size(v_bs_5780_);
    v___x_5787_ = 0usize;
    v___x_5788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_5779_,
        v___f_5785_,
        v_sz_5786_,
        v___x_5787_,
        v_bs_5780_,
    );
    return v___x_5788_;
}
pub unsafe fn l_Lean_IR_modifyJPsM(
    mut v_m_5789_: *mut LeanObject,
    mut v_inst_5790_: *mut LeanObject,
    mut v_bs_5791_: *mut LeanObject,
    mut v_f_5792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5797_: usize = 0;
    let mut v___x_5798_: usize = 0;
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_5793_ = lean_ctor_get(v_inst_5790_, 0);
    v_toBind_5794_ = lean_ctor_get(v_inst_5790_, 1);
    v_toPure_5795_ = lean_ctor_get(v_toApplicative_5793_, 1);
    lean_inc(v_toBind_5794_);
    lean_inc(v_toPure_5795_);
    v___f_5796_ = lean_alloc_closure(
        l_Lean_IR_modifyJPsM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_5796_, 0, v_toPure_5795_);
    lean_closure_set(v___f_5796_, 1, v_f_5792_);
    lean_closure_set(v___f_5796_, 2, v_toBind_5794_);
    v_sz_5797_ = lean_array_size(v_bs_5791_);
    v___x_5798_ = 0usize;
    v___x_5799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_inst_5790_,
        v___f_5796_,
        v_sz_5797_,
        v___x_5798_,
        v_bs_5791_,
    );
    return v___x_5799_;
}
pub unsafe fn l_Lean_IR_Decl_ctorIdx(mut v_x_5800_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_5800_) == 0 {
        let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
        v___x_5801_ = lean_unsigned_to_nat(0);
        return v___x_5801_;
    } else {
        let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
        v___x_5802_ = lean_unsigned_to_nat(1);
        return v___x_5802_;
    }
}
pub unsafe fn l_Lean_IR_Decl_ctorIdx___boxed(mut v_x_5803_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5804_: *mut LeanObject = core::ptr::null_mut();
    v_res_5804_ = l_Lean_IR_Decl_ctorIdx(v_x_5803_);
    lean_dec_ref(v_x_5803_);
    return v_res_5804_;
}
pub unsafe fn l_Lean_IR_Decl_ctorElim___redArg(
    mut v_t_5805_: *mut LeanObject,
    mut v_k_5806_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5805_) == 0 {
        let mut v_f_5807_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_5808_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_5809_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_5810_: *mut LeanObject = core::ptr::null_mut();
        let mut v_info_5811_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
        v_f_5807_ = lean_ctor_get(v_t_5805_, 0);
        lean_inc(v_f_5807_);
        v_xs_5808_ = lean_ctor_get(v_t_5805_, 1);
        lean_inc_ref(v_xs_5808_);
        v_type_5809_ = lean_ctor_get(v_t_5805_, 2);
        lean_inc(v_type_5809_);
        v_body_5810_ = lean_ctor_get(v_t_5805_, 3);
        lean_inc(v_body_5810_);
        v_info_5811_ = lean_ctor_get(v_t_5805_, 4);
        lean_inc(v_info_5811_);
        lean_dec_ref_known(v_t_5805_, 5);
        v___x_5812_ = lean_apply_5(
            v_k_5806_,
            v_f_5807_,
            v_xs_5808_,
            v_type_5809_,
            v_body_5810_,
            v_info_5811_,
        );
        return v___x_5812_;
    } else {
        let mut v_f_5813_: *mut LeanObject = core::ptr::null_mut();
        let mut v_xs_5814_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_5815_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ext_5816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5817_: *mut LeanObject = core::ptr::null_mut();
        v_f_5813_ = lean_ctor_get(v_t_5805_, 0);
        lean_inc(v_f_5813_);
        v_xs_5814_ = lean_ctor_get(v_t_5805_, 1);
        lean_inc_ref(v_xs_5814_);
        v_type_5815_ = lean_ctor_get(v_t_5805_, 2);
        lean_inc(v_type_5815_);
        v_ext_5816_ = lean_ctor_get(v_t_5805_, 3);
        lean_inc(v_ext_5816_);
        lean_dec_ref_known(v_t_5805_, 4);
        v___x_5817_ = lean_apply_4(v_k_5806_, v_f_5813_, v_xs_5814_, v_type_5815_, v_ext_5816_);
        return v___x_5817_;
    }
}
pub unsafe fn l_Lean_IR_Decl_ctorElim(
    mut v_motive_5818_: *mut LeanObject,
    mut v_ctorIdx_5819_: *mut LeanObject,
    mut v_t_5820_: *mut LeanObject,
    mut v_h_5821_: *mut LeanObject,
    mut v_k_5822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    v___x_5823_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5820_, v_k_5822_);
    return v___x_5823_;
}
pub unsafe fn l_Lean_IR_Decl_ctorElim___boxed(
    mut v_motive_5824_: *mut LeanObject,
    mut v_ctorIdx_5825_: *mut LeanObject,
    mut v_t_5826_: *mut LeanObject,
    mut v_h_5827_: *mut LeanObject,
    mut v_k_5828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5829_: *mut LeanObject = core::ptr::null_mut();
    v_res_5829_ = l_Lean_IR_Decl_ctorElim(
        v_motive_5824_,
        v_ctorIdx_5825_,
        v_t_5826_,
        v_h_5827_,
        v_k_5828_,
    );
    lean_dec(v_ctorIdx_5825_);
    return v_res_5829_;
}
pub unsafe fn l_Lean_IR_Decl_fdecl_elim___redArg(
    mut v_t_5830_: *mut LeanObject,
    mut v_fdecl_5831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5832_: *mut LeanObject = core::ptr::null_mut();
    v___x_5832_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5830_, v_fdecl_5831_);
    return v___x_5832_;
}
pub unsafe fn l_Lean_IR_Decl_fdecl_elim(
    mut v_motive_5833_: *mut LeanObject,
    mut v_t_5834_: *mut LeanObject,
    mut v_h_5835_: *mut LeanObject,
    mut v_fdecl_5836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    v___x_5837_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5834_, v_fdecl_5836_);
    return v___x_5837_;
}
pub unsafe fn l_Lean_IR_Decl_extern_elim___redArg(
    mut v_t_5838_: *mut LeanObject,
    mut v_extern_5839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    v___x_5840_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5838_, v_extern_5839_);
    return v___x_5840_;
}
pub unsafe fn l_Lean_IR_Decl_extern_elim(
    mut v_motive_5841_: *mut LeanObject,
    mut v_t_5842_: *mut LeanObject,
    mut v_h_5843_: *mut LeanObject,
    mut v_extern_5844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    v___x_5845_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5842_, v_extern_5844_);
    return v___x_5845_;
}
pub unsafe fn l_Lean_IR_Decl_name(mut v_x_5855_: *mut LeanObject) -> *mut LeanObject {
    let mut v_f_5856_: *mut LeanObject = core::ptr::null_mut();
    v_f_5856_ = lean_ctor_get(v_x_5855_, 0);
    lean_inc(v_f_5856_);
    return v_f_5856_;
}
pub unsafe fn l_Lean_IR_Decl_name___boxed(mut v_x_5857_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5858_: *mut LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_IR_Decl_name(v_x_5857_);
    lean_dec_ref(v_x_5857_);
    return v_res_5858_;
}
pub unsafe fn l_Lean_IR_Decl_params(mut v_x_5859_: *mut LeanObject) -> *mut LeanObject {
    let mut v_xs_5860_: *mut LeanObject = core::ptr::null_mut();
    v_xs_5860_ = lean_ctor_get(v_x_5859_, 1);
    lean_inc_ref(v_xs_5860_);
    return v_xs_5860_;
}
pub unsafe fn l_Lean_IR_Decl_params___boxed(mut v_x_5861_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5862_: *mut LeanObject = core::ptr::null_mut();
    v_res_5862_ = l_Lean_IR_Decl_params(v_x_5861_);
    lean_dec_ref(v_x_5861_);
    return v_res_5862_;
}
pub unsafe fn l_Lean_IR_Decl_resultType(mut v_x_5863_: *mut LeanObject) -> *mut LeanObject {
    let mut v_type_5864_: *mut LeanObject = core::ptr::null_mut();
    v_type_5864_ = lean_ctor_get(v_x_5863_, 2);
    lean_inc(v_type_5864_);
    return v_type_5864_;
}
pub unsafe fn l_Lean_IR_Decl_resultType___boxed(mut v_x_5865_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5866_: *mut LeanObject = core::ptr::null_mut();
    v_res_5866_ = l_Lean_IR_Decl_resultType(v_x_5865_);
    lean_dec_ref(v_x_5865_);
    return v_res_5866_;
}
pub unsafe fn l_Lean_IR_Decl_isExtern(mut v_x_5867_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_5867_) == 1 {
        let mut v___x_5868_: u8 = 0;
        v___x_5868_ = 1;
        return v___x_5868_;
    } else {
        let mut v___x_5869_: u8 = 0;
        v___x_5869_ = 0;
        return v___x_5869_;
    }
}
pub unsafe fn l_Lean_IR_Decl_isExtern___boxed(mut v_x_5870_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5871_: u8 = 0;
    let mut v_r_5872_: *mut LeanObject = core::ptr::null_mut();
    v_res_5871_ = l_Lean_IR_Decl_isExtern(v_x_5870_);
    lean_dec_ref(v_x_5870_);
    v_r_5872_ = lean_box((v_res_5871_) as usize);
    return v_r_5872_;
}
pub unsafe fn l_Lean_IR_Decl_getInfo(mut v_x_5873_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_5873_) == 0 {
        let mut v_info_5874_: *mut LeanObject = core::ptr::null_mut();
        v_info_5874_ = lean_ctor_get(v_x_5873_, 4);
        lean_inc(v_info_5874_);
        return v_info_5874_;
    } else {
        let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
        v___x_5875_ = lean_box(0);
        return v___x_5875_;
    }
}
pub unsafe fn l_Lean_IR_Decl_getInfo___boxed(mut v_x_5876_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_5877_: *mut LeanObject = core::ptr::null_mut();
    v_res_5877_ = l_Lean_IR_Decl_getInfo(v_x_5876_);
    lean_dec_ref(v_x_5876_);
    return v_res_5877_;
}
pub unsafe fn l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(
    mut v_msg_5878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    v___x_5879_ = l_Lean_IR_instInhabitedDecl_default;
    v___x_5880_ = lean_panic_fn_borrowed(v___x_5879_, v_msg_5878_);
    return v___x_5880_;
}
pub unsafe fn _init_l_Lean_IR_Decl_updateBody_x21___closed__3() -> *mut LeanObject {
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    v___x_5884_ = l_Lean_IR_Decl_updateBody_x21___closed__2;
    v___x_5885_ = lean_unsigned_to_nat(9);
    v___x_5886_ = lean_unsigned_to_nat(382);
    v___x_5887_ = l_Lean_IR_Decl_updateBody_x21___closed__1;
    v___x_5888_ = l_Lean_IR_Decl_updateBody_x21___closed__0;
    v___x_5889_ = l_mkPanicMessageWithDecl(
        v___x_5888_,
        v___x_5887_,
        v___x_5886_,
        v___x_5885_,
        v___x_5884_,
    );
    return v___x_5889_;
}
pub unsafe fn l_Lean_IR_Decl_updateBody_x21(
    mut v_d_5890_: *mut LeanObject,
    mut v_bNew_5891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut v_unused_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_d_5890_) == 0 {
                    v_f_5892_ = lean_ctor_get(v_d_5890_, 0);
                    v_xs_5893_ = lean_ctor_get(v_d_5890_, 1);
                    v_type_5894_ = lean_ctor_get(v_d_5890_, 2);
                    v_info_5895_ = lean_ctor_get(v_d_5890_, 4);
                    v_isSharedCheck_5902_ = (!lean_is_exclusive(v_d_5890_)) as u8;
                    if v_isSharedCheck_5902_ == 0 {
                        v_unused_5903_ = lean_ctor_get(v_d_5890_, 3);
                        lean_dec(v_unused_5903_);
                        v___x_5897_ = v_d_5890_;
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_info_5895_);
                        lean_inc(v_type_5894_);
                        lean_inc(v_xs_5893_);
                        lean_inc(v_f_5892_);
                        lean_dec(v_d_5890_);
                        v___x_5897_ = lean_box(0);
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_bNew_5891_);
                    lean_dec_ref(v_d_5890_);
                    v___x_5904_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_Decl_updateBody_x21___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_IR_Decl_updateBody_x21___closed__3_once),
                        _init_l_Lean_IR_Decl_updateBody_x21___closed__3,
                    );
                    v___x_5905_ = l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(v___x_5904_);
                    return v___x_5905_;
                }
            }
            1 => {
                if v_isShared_5898_ == 0 {
                    lean_ctor_set(v___x_5897_, 3, v_bNew_5891_);
                    v___x_5900_ = v___x_5897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_f_5892_);
                    lean_ctor_set(v_reuseFailAlloc_5901_, 1, v_xs_5893_);
                    lean_ctor_set(v_reuseFailAlloc_5901_, 2, v_type_5894_);
                    lean_ctor_set(v_reuseFailAlloc_5901_, 3, v_bNew_5891_);
                    lean_ctor_set(v_reuseFailAlloc_5901_, 4, v_info_5895_);
                    v___x_5900_ = v_reuseFailAlloc_5901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_mkDummyExternDecl(
    mut v_f_5906_: *mut LeanObject,
    mut v_xs_5907_: *mut LeanObject,
    mut v_ty_5908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    v___x_5909_ = lean_box(12);
    v___x_5910_ = lean_box(0);
    v___x_5911_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_5911_, 0, v_f_5906_);
    lean_ctor_set(v___x_5911_, 1, v_xs_5907_);
    lean_ctor_set(v___x_5911_, 2, v_ty_5908_);
    lean_ctor_set(v___x_5911_, 3, v___x_5909_);
    lean_ctor_set(v___x_5911_, 4, v___x_5910_);
    return v___x_5911_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
    mut v_k_5912_: *mut LeanObject,
    mut v_v_5913_: *mut LeanObject,
    mut v_t_5914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v___x_5923_: u8 = 0;
    let mut v___x_5924_: u8 = 0;
    let mut v_impl_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5943_: u8 = 0;
    let mut v_size_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: u8 = 0;
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5955_: u8 = 0;
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5980_: u8 = 0;
    let mut v_unused_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5993_: u8 = 0;
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5997_: u8 = 0;
    let mut v_unused_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6004_: u8 = 0;
    let mut v_unused_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v_k_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6021_: u8 = 0;
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6032_: u8 = 0;
    let mut v_unused_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_unused_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6044_: u8 = 0;
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_unused_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: u8 = 0;
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6081_: u8 = 0;
    let mut v_size_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: u8 = 0;
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6093_: u8 = 0;
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_unused_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6133_: u8 = 0;
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6137_: u8 = 0;
    let mut v_unused_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6144_: u8 = 0;
    let mut v_unused_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6156_: u8 = 0;
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6164_: u8 = 0;
    let mut v_unused_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6172_: u8 = 0;
    let mut v_k_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6188_: u8 = 0;
    let mut v_unused_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6192_: u8 = 0;
    let mut v_unused_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6200_: u8 = 0;
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_5914_) == 0 {
                    v_size_5915_ = lean_ctor_get(v_t_5914_, 0);
                    v_k_5916_ = lean_ctor_get(v_t_5914_, 1);
                    v_v_5917_ = lean_ctor_get(v_t_5914_, 2);
                    v_l_5918_ = lean_ctor_get(v_t_5914_, 3);
                    v_r_5919_ = lean_ctor_get(v_t_5914_, 4);
                    v_isSharedCheck_6200_ = (!lean_is_exclusive(v_t_5914_)) as u8;
                    if v_isSharedCheck_6200_ == 0 {
                        v___x_5921_ = v_t_5914_;
                        v_isShared_5922_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_5919_);
                        lean_inc(v_l_5918_);
                        lean_inc(v_v_5917_);
                        lean_inc(v_k_5916_);
                        lean_inc(v_size_5915_);
                        lean_dec(v_t_5914_);
                        v___x_5921_ = lean_box(0);
                        v_isShared_5922_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6201_ = lean_unsigned_to_nat(1);
                    v___x_6202_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_6202_, 0, v___x_6201_);
                    lean_ctor_set(v___x_6202_, 1, v_k_5912_);
                    lean_ctor_set(v___x_6202_, 2, v_v_5913_);
                    lean_ctor_set(v___x_6202_, 3, v_t_5914_);
                    lean_ctor_set(v___x_6202_, 4, v_t_5914_);
                    return v___x_6202_;
                }
            }
            1 => {
                v___x_5923_ = lean_nat_dec_lt(v_k_5912_, v_k_5916_);
                if v___x_5923_ == 0 {
                    v___x_5924_ = lean_nat_dec_eq(v_k_5912_, v_k_5916_);
                    if v___x_5924_ == 0 {
                        lean_dec(v_size_5915_);
                        v_impl_5925_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_5912_, v_v_5913_, v_r_5919_);
                        v___x_5926_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_5918_) == 0 {
                            v_size_5927_ = lean_ctor_get(v_l_5918_, 0);
                            v_size_5928_ = lean_ctor_get(v_impl_5925_, 0);
                            lean_inc(v_size_5928_);
                            v_k_5929_ = lean_ctor_get(v_impl_5925_, 1);
                            lean_inc(v_k_5929_);
                            v_v_5930_ = lean_ctor_get(v_impl_5925_, 2);
                            lean_inc(v_v_5930_);
                            v_l_5931_ = lean_ctor_get(v_impl_5925_, 3);
                            lean_inc(v_l_5931_);
                            v_r_5932_ = lean_ctor_get(v_impl_5925_, 4);
                            lean_inc(v_r_5932_);
                            v___x_5933_ = lean_unsigned_to_nat(3);
                            v___x_5934_ = lean_nat_mul(v___x_5933_, v_size_5927_);
                            v___x_5935_ = lean_nat_dec_lt(v___x_5934_, v_size_5928_);
                            lean_dec(v___x_5934_);
                            if v___x_5935_ == 0 {
                                lean_dec(v_r_5932_);
                                lean_dec(v_l_5931_);
                                lean_dec(v_v_5930_);
                                lean_dec(v_k_5929_);
                                v___x_5936_ = lean_nat_add(v___x_5926_, v_size_5927_);
                                v___x_5937_ = lean_nat_add(v___x_5936_, v_size_5928_);
                                lean_dec(v_size_5928_);
                                lean_dec(v___x_5936_);
                                if v_isShared_5922_ == 0 {
                                    lean_ctor_set(v___x_5921_, 4, v_impl_5925_);
                                    lean_ctor_set(v___x_5921_, 0, v___x_5937_);
                                    v___x_5939_ = v___x_5921_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5940_, 0, v___x_5937_);
                                    lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_k_5916_);
                                    lean_ctor_set(v_reuseFailAlloc_5940_, 2, v_v_5917_);
                                    lean_ctor_set(v_reuseFailAlloc_5940_, 3, v_l_5918_);
                                    lean_ctor_set(v_reuseFailAlloc_5940_, 4, v_impl_5925_);
                                    v___x_5939_ = v_reuseFailAlloc_5940_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_6004_ = (!lean_is_exclusive(v_impl_5925_)) as u8;
                                if v_isSharedCheck_6004_ == 0 {
                                    v_unused_6005_ = lean_ctor_get(v_impl_5925_, 4);
                                    lean_dec(v_unused_6005_);
                                    v_unused_6006_ = lean_ctor_get(v_impl_5925_, 3);
                                    lean_dec(v_unused_6006_);
                                    v_unused_6007_ = lean_ctor_get(v_impl_5925_, 2);
                                    lean_dec(v_unused_6007_);
                                    v_unused_6008_ = lean_ctor_get(v_impl_5925_, 1);
                                    lean_dec(v_unused_6008_);
                                    v_unused_6009_ = lean_ctor_get(v_impl_5925_, 0);
                                    lean_dec(v_unused_6009_);
                                    v___x_5942_ = v_impl_5925_;
                                    v_isShared_5943_ = v_isSharedCheck_6004_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_5925_);
                                    v___x_5942_ = lean_box(0);
                                    v_isShared_5943_ = v_isSharedCheck_6004_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_6010_ = lean_ctor_get(v_impl_5925_, 3);
                            lean_inc(v_l_6010_);
                            if lean_obj_tag(v_l_6010_) == 0 {
                                v_r_6011_ = lean_ctor_get(v_impl_5925_, 4);
                                v_k_6012_ = lean_ctor_get(v_impl_5925_, 1);
                                v_v_6013_ = lean_ctor_get(v_impl_5925_, 2);
                                v_isSharedCheck_6036_ = (!lean_is_exclusive(v_impl_5925_)) as u8;
                                if v_isSharedCheck_6036_ == 0 {
                                    v_unused_6037_ = lean_ctor_get(v_impl_5925_, 3);
                                    lean_dec(v_unused_6037_);
                                    v_unused_6038_ = lean_ctor_get(v_impl_5925_, 0);
                                    lean_dec(v_unused_6038_);
                                    v___x_6015_ = v_impl_5925_;
                                    v_isShared_6016_ = v_isSharedCheck_6036_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_6011_);
                                    lean_inc(v_v_6013_);
                                    lean_inc(v_k_6012_);
                                    lean_dec(v_impl_5925_);
                                    v___x_6015_ = lean_box(0);
                                    v_isShared_6016_ = v_isSharedCheck_6036_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_6039_ = lean_ctor_get(v_impl_5925_, 4);
                                lean_inc(v_r_6039_);
                                if lean_obj_tag(v_r_6039_) == 0 {
                                    v_k_6040_ = lean_ctor_get(v_impl_5925_, 1);
                                    v_v_6041_ = lean_ctor_get(v_impl_5925_, 2);
                                    v_isSharedCheck_6052_ =
                                        (!lean_is_exclusive(v_impl_5925_)) as u8;
                                    if v_isSharedCheck_6052_ == 0 {
                                        v_unused_6053_ = lean_ctor_get(v_impl_5925_, 4);
                                        lean_dec(v_unused_6053_);
                                        v_unused_6054_ = lean_ctor_get(v_impl_5925_, 3);
                                        lean_dec(v_unused_6054_);
                                        v_unused_6055_ = lean_ctor_get(v_impl_5925_, 0);
                                        lean_dec(v_unused_6055_);
                                        v___x_6043_ = v_impl_5925_;
                                        v_isShared_6044_ = v_isSharedCheck_6052_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_v_6041_);
                                        lean_inc(v_k_6040_);
                                        lean_dec(v_impl_5925_);
                                        v___x_6043_ = lean_box(0);
                                        v_isShared_6044_ = v_isSharedCheck_6052_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_6056_ = lean_unsigned_to_nat(2);
                                    if v_isShared_5922_ == 0 {
                                        lean_ctor_set(v___x_5921_, 4, v_impl_5925_);
                                        lean_ctor_set(v___x_5921_, 3, v_r_6039_);
                                        lean_ctor_set(v___x_5921_, 0, v___x_6056_);
                                        v___x_6058_ = v___x_5921_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6059_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6059_, 0, v___x_6056_);
                                        lean_ctor_set(v_reuseFailAlloc_6059_, 1, v_k_5916_);
                                        lean_ctor_set(v_reuseFailAlloc_6059_, 2, v_v_5917_);
                                        lean_ctor_set(v_reuseFailAlloc_6059_, 3, v_r_6039_);
                                        lean_ctor_set(v_reuseFailAlloc_6059_, 4, v_impl_5925_);
                                        v___x_6058_ = v_reuseFailAlloc_6059_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_5917_);
                        lean_dec(v_k_5916_);
                        if v_isShared_5922_ == 0 {
                            lean_ctor_set(v___x_5921_, 2, v_v_5913_);
                            lean_ctor_set(v___x_5921_, 1, v_k_5912_);
                            v___x_6061_ = v___x_5921_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_6062_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_size_5915_);
                            lean_ctor_set(v_reuseFailAlloc_6062_, 1, v_k_5912_);
                            lean_ctor_set(v_reuseFailAlloc_6062_, 2, v_v_5913_);
                            lean_ctor_set(v_reuseFailAlloc_6062_, 3, v_l_5918_);
                            lean_ctor_set(v_reuseFailAlloc_6062_, 4, v_r_5919_);
                            v___x_6061_ = v_reuseFailAlloc_6062_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_5915_);
                    v_impl_6063_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_5912_, v_v_5913_, v_l_5918_);
                    v___x_6064_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_r_5919_) == 0 {
                        v_size_6065_ = lean_ctor_get(v_r_5919_, 0);
                        v_size_6066_ = lean_ctor_get(v_impl_6063_, 0);
                        lean_inc(v_size_6066_);
                        v_k_6067_ = lean_ctor_get(v_impl_6063_, 1);
                        lean_inc(v_k_6067_);
                        v_v_6068_ = lean_ctor_get(v_impl_6063_, 2);
                        lean_inc(v_v_6068_);
                        v_l_6069_ = lean_ctor_get(v_impl_6063_, 3);
                        lean_inc(v_l_6069_);
                        v_r_6070_ = lean_ctor_get(v_impl_6063_, 4);
                        lean_inc(v_r_6070_);
                        v___x_6071_ = lean_unsigned_to_nat(3);
                        v___x_6072_ = lean_nat_mul(v___x_6071_, v_size_6065_);
                        v___x_6073_ = lean_nat_dec_lt(v___x_6072_, v_size_6066_);
                        lean_dec(v___x_6072_);
                        if v___x_6073_ == 0 {
                            lean_dec(v_r_6070_);
                            lean_dec(v_l_6069_);
                            lean_dec(v_v_6068_);
                            lean_dec(v_k_6067_);
                            v___x_6074_ = lean_nat_add(v___x_6064_, v_size_6066_);
                            lean_dec(v_size_6066_);
                            v___x_6075_ = lean_nat_add(v___x_6074_, v_size_6065_);
                            lean_dec(v___x_6074_);
                            if v_isShared_5922_ == 0 {
                                lean_ctor_set(v___x_5921_, 3, v_impl_6063_);
                                lean_ctor_set(v___x_5921_, 0, v___x_6075_);
                                v___x_6077_ = v___x_5921_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_6078_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6075_);
                                lean_ctor_set(v_reuseFailAlloc_6078_, 1, v_k_5916_);
                                lean_ctor_set(v_reuseFailAlloc_6078_, 2, v_v_5917_);
                                lean_ctor_set(v_reuseFailAlloc_6078_, 3, v_impl_6063_);
                                lean_ctor_set(v_reuseFailAlloc_6078_, 4, v_r_5919_);
                                v___x_6077_ = v_reuseFailAlloc_6078_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_6144_ = (!lean_is_exclusive(v_impl_6063_)) as u8;
                            if v_isSharedCheck_6144_ == 0 {
                                v_unused_6145_ = lean_ctor_get(v_impl_6063_, 4);
                                lean_dec(v_unused_6145_);
                                v_unused_6146_ = lean_ctor_get(v_impl_6063_, 3);
                                lean_dec(v_unused_6146_);
                                v_unused_6147_ = lean_ctor_get(v_impl_6063_, 2);
                                lean_dec(v_unused_6147_);
                                v_unused_6148_ = lean_ctor_get(v_impl_6063_, 1);
                                lean_dec(v_unused_6148_);
                                v_unused_6149_ = lean_ctor_get(v_impl_6063_, 0);
                                lean_dec(v_unused_6149_);
                                v___x_6080_ = v_impl_6063_;
                                v_isShared_6081_ = v_isSharedCheck_6144_;
                                state = 24;
                                continue;
                            } else {
                                lean_dec(v_impl_6063_);
                                v___x_6080_ = lean_box(0);
                                v_isShared_6081_ = v_isSharedCheck_6144_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_6150_ = lean_ctor_get(v_impl_6063_, 3);
                        lean_inc(v_l_6150_);
                        if lean_obj_tag(v_l_6150_) == 0 {
                            v_r_6151_ = lean_ctor_get(v_impl_6063_, 4);
                            v_k_6152_ = lean_ctor_get(v_impl_6063_, 1);
                            v_v_6153_ = lean_ctor_get(v_impl_6063_, 2);
                            v_isSharedCheck_6164_ = (!lean_is_exclusive(v_impl_6063_)) as u8;
                            if v_isSharedCheck_6164_ == 0 {
                                v_unused_6165_ = lean_ctor_get(v_impl_6063_, 3);
                                lean_dec(v_unused_6165_);
                                v_unused_6166_ = lean_ctor_get(v_impl_6063_, 0);
                                lean_dec(v_unused_6166_);
                                v___x_6155_ = v_impl_6063_;
                                v_isShared_6156_ = v_isSharedCheck_6164_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_r_6151_);
                                lean_inc(v_v_6153_);
                                lean_inc(v_k_6152_);
                                lean_dec(v_impl_6063_);
                                v___x_6155_ = lean_box(0);
                                v_isShared_6156_ = v_isSharedCheck_6164_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_6167_ = lean_ctor_get(v_impl_6063_, 4);
                            lean_inc(v_r_6167_);
                            if lean_obj_tag(v_r_6167_) == 0 {
                                v_k_6168_ = lean_ctor_get(v_impl_6063_, 1);
                                v_v_6169_ = lean_ctor_get(v_impl_6063_, 2);
                                v_isSharedCheck_6192_ = (!lean_is_exclusive(v_impl_6063_)) as u8;
                                if v_isSharedCheck_6192_ == 0 {
                                    v_unused_6193_ = lean_ctor_get(v_impl_6063_, 4);
                                    lean_dec(v_unused_6193_);
                                    v_unused_6194_ = lean_ctor_get(v_impl_6063_, 3);
                                    lean_dec(v_unused_6194_);
                                    v_unused_6195_ = lean_ctor_get(v_impl_6063_, 0);
                                    lean_dec(v_unused_6195_);
                                    v___x_6171_ = v_impl_6063_;
                                    v_isShared_6172_ = v_isSharedCheck_6192_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_v_6169_);
                                    lean_inc(v_k_6168_);
                                    lean_dec(v_impl_6063_);
                                    v___x_6171_ = lean_box(0);
                                    v_isShared_6172_ = v_isSharedCheck_6192_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_6196_ = lean_unsigned_to_nat(2);
                                if v_isShared_5922_ == 0 {
                                    lean_ctor_set(v___x_5921_, 4, v_r_6167_);
                                    lean_ctor_set(v___x_5921_, 3, v_impl_6063_);
                                    lean_ctor_set(v___x_5921_, 0, v___x_6196_);
                                    v___x_6198_ = v___x_5921_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6199_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6199_, 0, v___x_6196_);
                                    lean_ctor_set(v_reuseFailAlloc_6199_, 1, v_k_5916_);
                                    lean_ctor_set(v_reuseFailAlloc_6199_, 2, v_v_5917_);
                                    lean_ctor_set(v_reuseFailAlloc_6199_, 3, v_impl_6063_);
                                    lean_ctor_set(v_reuseFailAlloc_6199_, 4, v_r_6167_);
                                    v___x_6198_ = v_reuseFailAlloc_6199_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_5939_;
            }
            3 => {
                v_size_5944_ = lean_ctor_get(v_l_5931_, 0);
                v_k_5945_ = lean_ctor_get(v_l_5931_, 1);
                v_v_5946_ = lean_ctor_get(v_l_5931_, 2);
                v_l_5947_ = lean_ctor_get(v_l_5931_, 3);
                v_r_5948_ = lean_ctor_get(v_l_5931_, 4);
                v_size_5949_ = lean_ctor_get(v_r_5932_, 0);
                v___x_5950_ = lean_unsigned_to_nat(2);
                v___x_5951_ = lean_nat_mul(v___x_5950_, v_size_5949_);
                v___x_5952_ = lean_nat_dec_lt(v_size_5944_, v___x_5951_);
                lean_dec(v___x_5951_);
                if v___x_5952_ == 0 {
                    lean_inc(v_r_5948_);
                    lean_inc(v_l_5947_);
                    lean_inc(v_v_5946_);
                    lean_inc(v_k_5945_);
                    v_isSharedCheck_5980_ = (!lean_is_exclusive(v_l_5931_)) as u8;
                    if v_isSharedCheck_5980_ == 0 {
                        v_unused_5981_ = lean_ctor_get(v_l_5931_, 4);
                        lean_dec(v_unused_5981_);
                        v_unused_5982_ = lean_ctor_get(v_l_5931_, 3);
                        lean_dec(v_unused_5982_);
                        v_unused_5983_ = lean_ctor_get(v_l_5931_, 2);
                        lean_dec(v_unused_5983_);
                        v_unused_5984_ = lean_ctor_get(v_l_5931_, 1);
                        lean_dec(v_unused_5984_);
                        v_unused_5985_ = lean_ctor_get(v_l_5931_, 0);
                        lean_dec(v_unused_5985_);
                        v___x_5954_ = v_l_5931_;
                        v_isShared_5955_ = v_isSharedCheck_5980_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_5931_);
                        v___x_5954_ = lean_box(0);
                        v_isShared_5955_ = v_isSharedCheck_5980_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5921_);
                    v___x_5986_ = lean_nat_add(v___x_5926_, v_size_5927_);
                    v___x_5987_ = lean_nat_add(v___x_5986_, v_size_5928_);
                    lean_dec(v_size_5928_);
                    v___x_5988_ = lean_nat_add(v___x_5986_, v_size_5944_);
                    lean_dec(v___x_5986_);
                    lean_inc_ref(v_l_5918_);
                    if v_isShared_5943_ == 0 {
                        lean_ctor_set(v___x_5942_, 4, v_l_5931_);
                        lean_ctor_set(v___x_5942_, 3, v_l_5918_);
                        lean_ctor_set(v___x_5942_, 2, v_v_5917_);
                        lean_ctor_set(v___x_5942_, 1, v_k_5916_);
                        lean_ctor_set(v___x_5942_, 0, v___x_5988_);
                        v___x_5990_ = v___x_5942_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6003_, 0, v___x_5988_);
                        lean_ctor_set(v_reuseFailAlloc_6003_, 1, v_k_5916_);
                        lean_ctor_set(v_reuseFailAlloc_6003_, 2, v_v_5917_);
                        lean_ctor_set(v_reuseFailAlloc_6003_, 3, v_l_5918_);
                        lean_ctor_set(v_reuseFailAlloc_6003_, 4, v_l_5931_);
                        v___x_5990_ = v_reuseFailAlloc_6003_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5956_ = lean_nat_add(v___x_5926_, v_size_5927_);
                v___x_5957_ = lean_nat_add(v___x_5956_, v_size_5928_);
                lean_dec(v_size_5928_);
                if lean_obj_tag(v_l_5947_) == 0 {
                    v_size_5978_ = lean_ctor_get(v_l_5947_, 0);
                    lean_inc(v_size_5978_);
                    v___y_5970_ = v_size_5978_;
                    state = 8;
                    continue;
                } else {
                    v___x_5979_ = lean_unsigned_to_nat(0);
                    v___y_5970_ = v___x_5979_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_5962_ = lean_nat_add(v___y_5960_, v___y_5961_);
                lean_dec(v___y_5961_);
                lean_dec(v___y_5960_);
                if v_isShared_5955_ == 0 {
                    lean_ctor_set(v___x_5954_, 4, v_r_5932_);
                    lean_ctor_set(v___x_5954_, 3, v_r_5948_);
                    lean_ctor_set(v___x_5954_, 2, v_v_5930_);
                    lean_ctor_set(v___x_5954_, 1, v_k_5929_);
                    lean_ctor_set(v___x_5954_, 0, v___x_5962_);
                    v___x_5964_ = v___x_5954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5968_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5968_, 0, v___x_5962_);
                    lean_ctor_set(v_reuseFailAlloc_5968_, 1, v_k_5929_);
                    lean_ctor_set(v_reuseFailAlloc_5968_, 2, v_v_5930_);
                    lean_ctor_set(v_reuseFailAlloc_5968_, 3, v_r_5948_);
                    lean_ctor_set(v_reuseFailAlloc_5968_, 4, v_r_5932_);
                    v___x_5964_ = v_reuseFailAlloc_5968_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5943_ == 0 {
                    lean_ctor_set(v___x_5942_, 4, v___x_5964_);
                    lean_ctor_set(v___x_5942_, 3, v___y_5959_);
                    lean_ctor_set(v___x_5942_, 2, v_v_5946_);
                    lean_ctor_set(v___x_5942_, 1, v_k_5945_);
                    lean_ctor_set(v___x_5942_, 0, v___x_5957_);
                    v___x_5966_ = v___x_5942_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5967_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5967_, 0, v___x_5957_);
                    lean_ctor_set(v_reuseFailAlloc_5967_, 1, v_k_5945_);
                    lean_ctor_set(v_reuseFailAlloc_5967_, 2, v_v_5946_);
                    lean_ctor_set(v_reuseFailAlloc_5967_, 3, v___y_5959_);
                    lean_ctor_set(v_reuseFailAlloc_5967_, 4, v___x_5964_);
                    v___x_5966_ = v_reuseFailAlloc_5967_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5966_;
            }
            8 => {
                v___x_5971_ = lean_nat_add(v___x_5956_, v___y_5970_);
                lean_dec(v___y_5970_);
                lean_dec(v___x_5956_);
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 4, v_l_5947_);
                    lean_ctor_set(v___x_5921_, 0, v___x_5971_);
                    v___x_5973_ = v___x_5921_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 0, v___x_5971_);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_k_5916_);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 2, v_v_5917_);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 3, v_l_5918_);
                    lean_ctor_set(v_reuseFailAlloc_5977_, 4, v_l_5947_);
                    v___x_5973_ = v_reuseFailAlloc_5977_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5974_ = lean_nat_add(v___x_5926_, v_size_5949_);
                if lean_obj_tag(v_r_5948_) == 0 {
                    v_size_5975_ = lean_ctor_get(v_r_5948_, 0);
                    lean_inc(v_size_5975_);
                    v___y_5959_ = v___x_5973_;
                    v___y_5960_ = v___x_5974_;
                    v___y_5961_ = v_size_5975_;
                    state = 5;
                    continue;
                } else {
                    v___x_5976_ = lean_unsigned_to_nat(0);
                    v___y_5959_ = v___x_5973_;
                    v___y_5960_ = v___x_5974_;
                    v___y_5961_ = v___x_5976_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_5997_ = (!lean_is_exclusive(v_l_5918_)) as u8;
                if v_isSharedCheck_5997_ == 0 {
                    v_unused_5998_ = lean_ctor_get(v_l_5918_, 4);
                    lean_dec(v_unused_5998_);
                    v_unused_5999_ = lean_ctor_get(v_l_5918_, 3);
                    lean_dec(v_unused_5999_);
                    v_unused_6000_ = lean_ctor_get(v_l_5918_, 2);
                    lean_dec(v_unused_6000_);
                    v_unused_6001_ = lean_ctor_get(v_l_5918_, 1);
                    lean_dec(v_unused_6001_);
                    v_unused_6002_ = lean_ctor_get(v_l_5918_, 0);
                    lean_dec(v_unused_6002_);
                    v___x_5992_ = v_l_5918_;
                    v_isShared_5993_ = v_isSharedCheck_5997_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_l_5918_);
                    v___x_5992_ = lean_box(0);
                    v_isShared_5993_ = v_isSharedCheck_5997_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5993_ == 0 {
                    lean_ctor_set(v___x_5992_, 4, v_r_5932_);
                    lean_ctor_set(v___x_5992_, 3, v___x_5990_);
                    lean_ctor_set(v___x_5992_, 2, v_v_5930_);
                    lean_ctor_set(v___x_5992_, 1, v_k_5929_);
                    lean_ctor_set(v___x_5992_, 0, v___x_5987_);
                    v___x_5995_ = v___x_5992_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5996_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5996_, 0, v___x_5987_);
                    lean_ctor_set(v_reuseFailAlloc_5996_, 1, v_k_5929_);
                    lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_v_5930_);
                    lean_ctor_set(v_reuseFailAlloc_5996_, 3, v___x_5990_);
                    lean_ctor_set(v_reuseFailAlloc_5996_, 4, v_r_5932_);
                    v___x_5995_ = v_reuseFailAlloc_5996_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5995_;
            }
            13 => {
                v_k_6017_ = lean_ctor_get(v_l_6010_, 1);
                v_v_6018_ = lean_ctor_get(v_l_6010_, 2);
                v_isSharedCheck_6032_ = (!lean_is_exclusive(v_l_6010_)) as u8;
                if v_isSharedCheck_6032_ == 0 {
                    v_unused_6033_ = lean_ctor_get(v_l_6010_, 4);
                    lean_dec(v_unused_6033_);
                    v_unused_6034_ = lean_ctor_get(v_l_6010_, 3);
                    lean_dec(v_unused_6034_);
                    v_unused_6035_ = lean_ctor_get(v_l_6010_, 0);
                    lean_dec(v_unused_6035_);
                    v___x_6020_ = v_l_6010_;
                    v_isShared_6021_ = v_isSharedCheck_6032_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_v_6018_);
                    lean_inc(v_k_6017_);
                    lean_dec(v_l_6010_);
                    v___x_6020_ = lean_box(0);
                    v_isShared_6021_ = v_isSharedCheck_6032_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_6022_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_6011_, 2);
                if v_isShared_6021_ == 0 {
                    lean_ctor_set(v___x_6020_, 4, v_r_6011_);
                    lean_ctor_set(v___x_6020_, 3, v_r_6011_);
                    lean_ctor_set(v___x_6020_, 2, v_v_5917_);
                    lean_ctor_set(v___x_6020_, 1, v_k_5916_);
                    lean_ctor_set(v___x_6020_, 0, v___x_5926_);
                    v___x_6024_ = v___x_6020_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_5926_);
                    lean_ctor_set(v_reuseFailAlloc_6031_, 1, v_k_5916_);
                    lean_ctor_set(v_reuseFailAlloc_6031_, 2, v_v_5917_);
                    lean_ctor_set(v_reuseFailAlloc_6031_, 3, v_r_6011_);
                    lean_ctor_set(v_reuseFailAlloc_6031_, 4, v_r_6011_);
                    v___x_6024_ = v_reuseFailAlloc_6031_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_inc(v_r_6011_);
                if v_isShared_6016_ == 0 {
                    lean_ctor_set(v___x_6015_, 3, v_r_6011_);
                    lean_ctor_set(v___x_6015_, 0, v___x_5926_);
                    v___x_6026_ = v___x_6015_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6030_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 0, v___x_5926_);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 1, v_k_6012_);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 2, v_v_6013_);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 3, v_r_6011_);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 4, v_r_6011_);
                    v___x_6026_ = v_reuseFailAlloc_6030_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 4, v___x_6026_);
                    lean_ctor_set(v___x_5921_, 3, v___x_6024_);
                    lean_ctor_set(v___x_5921_, 2, v_v_6018_);
                    lean_ctor_set(v___x_5921_, 1, v_k_6017_);
                    lean_ctor_set(v___x_5921_, 0, v___x_6022_);
                    v___x_6028_ = v___x_5921_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6029_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6029_, 0, v___x_6022_);
                    lean_ctor_set(v_reuseFailAlloc_6029_, 1, v_k_6017_);
                    lean_ctor_set(v_reuseFailAlloc_6029_, 2, v_v_6018_);
                    lean_ctor_set(v_reuseFailAlloc_6029_, 3, v___x_6024_);
                    lean_ctor_set(v_reuseFailAlloc_6029_, 4, v___x_6026_);
                    v___x_6028_ = v_reuseFailAlloc_6029_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6028_;
            }
            18 => {
                v___x_6045_ = lean_unsigned_to_nat(3);
                if v_isShared_6044_ == 0 {
                    lean_ctor_set(v___x_6043_, 4, v_l_6010_);
                    lean_ctor_set(v___x_6043_, 2, v_v_5917_);
                    lean_ctor_set(v___x_6043_, 1, v_k_5916_);
                    lean_ctor_set(v___x_6043_, 0, v___x_5926_);
                    v___x_6047_ = v___x_6043_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6051_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 0, v___x_5926_);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 1, v_k_5916_);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 2, v_v_5917_);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 3, v_l_6010_);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 4, v_l_6010_);
                    v___x_6047_ = v_reuseFailAlloc_6051_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 4, v_r_6039_);
                    lean_ctor_set(v___x_5921_, 3, v___x_6047_);
                    lean_ctor_set(v___x_5921_, 2, v_v_6041_);
                    lean_ctor_set(v___x_5921_, 1, v_k_6040_);
                    lean_ctor_set(v___x_5921_, 0, v___x_6045_);
                    v___x_6049_ = v___x_5921_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6050_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6050_, 0, v___x_6045_);
                    lean_ctor_set(v_reuseFailAlloc_6050_, 1, v_k_6040_);
                    lean_ctor_set(v_reuseFailAlloc_6050_, 2, v_v_6041_);
                    lean_ctor_set(v_reuseFailAlloc_6050_, 3, v___x_6047_);
                    lean_ctor_set(v_reuseFailAlloc_6050_, 4, v_r_6039_);
                    v___x_6049_ = v_reuseFailAlloc_6050_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6049_;
            }
            21 => {
                return v___x_6058_;
            }
            22 => {
                return v___x_6061_;
            }
            23 => {
                return v___x_6077_;
            }
            24 => {
                v_size_6082_ = lean_ctor_get(v_l_6069_, 0);
                v_size_6083_ = lean_ctor_get(v_r_6070_, 0);
                v_k_6084_ = lean_ctor_get(v_r_6070_, 1);
                v_v_6085_ = lean_ctor_get(v_r_6070_, 2);
                v_l_6086_ = lean_ctor_get(v_r_6070_, 3);
                v_r_6087_ = lean_ctor_get(v_r_6070_, 4);
                v___x_6088_ = lean_unsigned_to_nat(2);
                v___x_6089_ = lean_nat_mul(v___x_6088_, v_size_6082_);
                v___x_6090_ = lean_nat_dec_lt(v_size_6083_, v___x_6089_);
                lean_dec(v___x_6089_);
                if v___x_6090_ == 0 {
                    lean_inc(v_r_6087_);
                    lean_inc(v_l_6086_);
                    lean_inc(v_v_6085_);
                    lean_inc(v_k_6084_);
                    v_isSharedCheck_6119_ = (!lean_is_exclusive(v_r_6070_)) as u8;
                    if v_isSharedCheck_6119_ == 0 {
                        v_unused_6120_ = lean_ctor_get(v_r_6070_, 4);
                        lean_dec(v_unused_6120_);
                        v_unused_6121_ = lean_ctor_get(v_r_6070_, 3);
                        lean_dec(v_unused_6121_);
                        v_unused_6122_ = lean_ctor_get(v_r_6070_, 2);
                        lean_dec(v_unused_6122_);
                        v_unused_6123_ = lean_ctor_get(v_r_6070_, 1);
                        lean_dec(v_unused_6123_);
                        v_unused_6124_ = lean_ctor_get(v_r_6070_, 0);
                        lean_dec(v_unused_6124_);
                        v___x_6092_ = v_r_6070_;
                        v_isShared_6093_ = v_isSharedCheck_6119_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_r_6070_);
                        v___x_6092_ = lean_box(0);
                        v_isShared_6093_ = v_isSharedCheck_6119_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5921_);
                    v___x_6125_ = lean_nat_add(v___x_6064_, v_size_6066_);
                    lean_dec(v_size_6066_);
                    v___x_6126_ = lean_nat_add(v___x_6125_, v_size_6065_);
                    lean_dec(v___x_6125_);
                    v___x_6127_ = lean_nat_add(v___x_6064_, v_size_6065_);
                    v___x_6128_ = lean_nat_add(v___x_6127_, v_size_6083_);
                    lean_dec(v___x_6127_);
                    lean_inc_ref(v_r_5919_);
                    if v_isShared_6081_ == 0 {
                        lean_ctor_set(v___x_6080_, 4, v_r_5919_);
                        lean_ctor_set(v___x_6080_, 3, v_r_6070_);
                        lean_ctor_set(v___x_6080_, 2, v_v_5917_);
                        lean_ctor_set(v___x_6080_, 1, v_k_5916_);
                        lean_ctor_set(v___x_6080_, 0, v___x_6128_);
                        v___x_6130_ = v___x_6080_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_6143_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6143_, 0, v___x_6128_);
                        lean_ctor_set(v_reuseFailAlloc_6143_, 1, v_k_5916_);
                        lean_ctor_set(v_reuseFailAlloc_6143_, 2, v_v_5917_);
                        lean_ctor_set(v_reuseFailAlloc_6143_, 3, v_r_6070_);
                        lean_ctor_set(v_reuseFailAlloc_6143_, 4, v_r_5919_);
                        v___x_6130_ = v_reuseFailAlloc_6143_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_6094_ = lean_nat_add(v___x_6064_, v_size_6066_);
                lean_dec(v_size_6066_);
                v___x_6095_ = lean_nat_add(v___x_6094_, v_size_6065_);
                lean_dec(v___x_6094_);
                v___x_6107_ = lean_nat_add(v___x_6064_, v_size_6082_);
                if lean_obj_tag(v_l_6086_) == 0 {
                    v_size_6117_ = lean_ctor_get(v_l_6086_, 0);
                    lean_inc(v_size_6117_);
                    v___y_6109_ = v_size_6117_;
                    state = 29;
                    continue;
                } else {
                    v___x_6118_ = lean_unsigned_to_nat(0);
                    v___y_6109_ = v___x_6118_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_6100_ = lean_nat_add(v___y_6098_, v___y_6099_);
                lean_dec(v___y_6099_);
                lean_dec(v___y_6098_);
                if v_isShared_6093_ == 0 {
                    lean_ctor_set(v___x_6092_, 4, v_r_5919_);
                    lean_ctor_set(v___x_6092_, 3, v_r_6087_);
                    lean_ctor_set(v___x_6092_, 2, v_v_5917_);
                    lean_ctor_set(v___x_6092_, 1, v_k_5916_);
                    lean_ctor_set(v___x_6092_, 0, v___x_6100_);
                    v___x_6102_ = v___x_6092_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6106_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6106_, 0, v___x_6100_);
                    lean_ctor_set(v_reuseFailAlloc_6106_, 1, v_k_5916_);
                    lean_ctor_set(v_reuseFailAlloc_6106_, 2, v_v_5917_);
                    lean_ctor_set(v_reuseFailAlloc_6106_, 3, v_r_6087_);
                    lean_ctor_set(v_reuseFailAlloc_6106_, 4, v_r_5919_);
                    v___x_6102_ = v_reuseFailAlloc_6106_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_6081_ == 0 {
                    lean_ctor_set(v___x_6080_, 4, v___x_6102_);
                    lean_ctor_set(v___x_6080_, 3, v___y_6097_);
                    lean_ctor_set(v___x_6080_, 2, v_v_6085_);
                    lean_ctor_set(v___x_6080_, 1, v_k_6084_);
                    lean_ctor_set(v___x_6080_, 0, v___x_6095_);
                    v___x_6104_ = v___x_6080_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6105_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6095_);
                    lean_ctor_set(v_reuseFailAlloc_6105_, 1, v_k_6084_);
                    lean_ctor_set(v_reuseFailAlloc_6105_, 2, v_v_6085_);
                    lean_ctor_set(v_reuseFailAlloc_6105_, 3, v___y_6097_);
                    lean_ctor_set(v_reuseFailAlloc_6105_, 4, v___x_6102_);
                    v___x_6104_ = v_reuseFailAlloc_6105_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6104_;
            }
            29 => {
                v___x_6110_ = lean_nat_add(v___x_6107_, v___y_6109_);
                lean_dec(v___y_6109_);
                lean_dec(v___x_6107_);
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 4, v_l_6086_);
                    lean_ctor_set(v___x_5921_, 3, v_l_6069_);
                    lean_ctor_set(v___x_5921_, 2, v_v_6068_);
                    lean_ctor_set(v___x_5921_, 1, v_k_6067_);
                    lean_ctor_set(v___x_5921_, 0, v___x_6110_);
                    v___x_6112_ = v___x_5921_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 0, v___x_6110_);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 1, v_k_6067_);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 2, v_v_6068_);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 3, v_l_6069_);
                    lean_ctor_set(v_reuseFailAlloc_6116_, 4, v_l_6086_);
                    v___x_6112_ = v_reuseFailAlloc_6116_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_6113_ = lean_nat_add(v___x_6064_, v_size_6065_);
                if lean_obj_tag(v_r_6087_) == 0 {
                    v_size_6114_ = lean_ctor_get(v_r_6087_, 0);
                    lean_inc(v_size_6114_);
                    v___y_6097_ = v___x_6112_;
                    v___y_6098_ = v___x_6113_;
                    v___y_6099_ = v_size_6114_;
                    state = 26;
                    continue;
                } else {
                    v___x_6115_ = lean_unsigned_to_nat(0);
                    v___y_6097_ = v___x_6112_;
                    v___y_6098_ = v___x_6113_;
                    v___y_6099_ = v___x_6115_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_6137_ = (!lean_is_exclusive(v_r_5919_)) as u8;
                if v_isSharedCheck_6137_ == 0 {
                    v_unused_6138_ = lean_ctor_get(v_r_5919_, 4);
                    lean_dec(v_unused_6138_);
                    v_unused_6139_ = lean_ctor_get(v_r_5919_, 3);
                    lean_dec(v_unused_6139_);
                    v_unused_6140_ = lean_ctor_get(v_r_5919_, 2);
                    lean_dec(v_unused_6140_);
                    v_unused_6141_ = lean_ctor_get(v_r_5919_, 1);
                    lean_dec(v_unused_6141_);
                    v_unused_6142_ = lean_ctor_get(v_r_5919_, 0);
                    lean_dec(v_unused_6142_);
                    v___x_6132_ = v_r_5919_;
                    v_isShared_6133_ = v_isSharedCheck_6137_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_r_5919_);
                    v___x_6132_ = lean_box(0);
                    v_isShared_6133_ = v_isSharedCheck_6137_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_6133_ == 0 {
                    lean_ctor_set(v___x_6132_, 4, v___x_6130_);
                    lean_ctor_set(v___x_6132_, 3, v_l_6069_);
                    lean_ctor_set(v___x_6132_, 2, v_v_6068_);
                    lean_ctor_set(v___x_6132_, 1, v_k_6067_);
                    lean_ctor_set(v___x_6132_, 0, v___x_6126_);
                    v___x_6135_ = v___x_6132_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6136_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 0, v___x_6126_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 1, v_k_6067_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 2, v_v_6068_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 3, v_l_6069_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 4, v___x_6130_);
                    v___x_6135_ = v_reuseFailAlloc_6136_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6135_;
            }
            34 => {
                v___x_6157_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_6151_);
                if v_isShared_6156_ == 0 {
                    lean_ctor_set(v___x_6155_, 3, v_r_6151_);
                    lean_ctor_set(v___x_6155_, 2, v_v_5917_);
                    lean_ctor_set(v___x_6155_, 1, v_k_5916_);
                    lean_ctor_set(v___x_6155_, 0, v___x_6064_);
                    v___x_6159_ = v___x_6155_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6163_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6163_, 0, v___x_6064_);
                    lean_ctor_set(v_reuseFailAlloc_6163_, 1, v_k_5916_);
                    lean_ctor_set(v_reuseFailAlloc_6163_, 2, v_v_5917_);
                    lean_ctor_set(v_reuseFailAlloc_6163_, 3, v_r_6151_);
                    lean_ctor_set(v_reuseFailAlloc_6163_, 4, v_r_6151_);
                    v___x_6159_ = v_reuseFailAlloc_6163_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 4, v___x_6159_);
                    lean_ctor_set(v___x_5921_, 3, v_l_6150_);
                    lean_ctor_set(v___x_5921_, 2, v_v_6153_);
                    lean_ctor_set(v___x_5921_, 1, v_k_6152_);
                    lean_ctor_set(v___x_5921_, 0, v___x_6157_);
                    v___x_6161_ = v___x_5921_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6162_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6162_, 0, v___x_6157_);
                    lean_ctor_set(v_reuseFailAlloc_6162_, 1, v_k_6152_);
                    lean_ctor_set(v_reuseFailAlloc_6162_, 2, v_v_6153_);
                    lean_ctor_set(v_reuseFailAlloc_6162_, 3, v_l_6150_);
                    lean_ctor_set(v_reuseFailAlloc_6162_, 4, v___x_6159_);
                    v___x_6161_ = v_reuseFailAlloc_6162_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_6161_;
            }
            37 => {
                v_k_6173_ = lean_ctor_get(v_r_6167_, 1);
                v_v_6174_ = lean_ctor_get(v_r_6167_, 2);
                v_isSharedCheck_6188_ = (!lean_is_exclusive(v_r_6167_)) as u8;
                if v_isSharedCheck_6188_ == 0 {
                    v_unused_6189_ = lean_ctor_get(v_r_6167_, 4);
                    lean_dec(v_unused_6189_);
                    v_unused_6190_ = lean_ctor_get(v_r_6167_, 3);
                    lean_dec(v_unused_6190_);
                    v_unused_6191_ = lean_ctor_get(v_r_6167_, 0);
                    lean_dec(v_unused_6191_);
                    v___x_6176_ = v_r_6167_;
                    v_isShared_6177_ = v_isSharedCheck_6188_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_v_6174_);
                    lean_inc(v_k_6173_);
                    lean_dec(v_r_6167_);
                    v___x_6176_ = lean_box(0);
                    v_isShared_6177_ = v_isSharedCheck_6188_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_6178_ = lean_unsigned_to_nat(3);
                if v_isShared_6177_ == 0 {
                    lean_ctor_set(v___x_6176_, 4, v_l_6150_);
                    lean_ctor_set(v___x_6176_, 3, v_l_6150_);
                    lean_ctor_set(v___x_6176_, 2, v_v_6169_);
                    lean_ctor_set(v___x_6176_, 1, v_k_6168_);
                    lean_ctor_set(v___x_6176_, 0, v___x_6064_);
                    v___x_6180_ = v___x_6176_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6187_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6187_, 0, v___x_6064_);
                    lean_ctor_set(v_reuseFailAlloc_6187_, 1, v_k_6168_);
                    lean_ctor_set(v_reuseFailAlloc_6187_, 2, v_v_6169_);
                    lean_ctor_set(v_reuseFailAlloc_6187_, 3, v_l_6150_);
                    lean_ctor_set(v_reuseFailAlloc_6187_, 4, v_l_6150_);
                    v___x_6180_ = v_reuseFailAlloc_6187_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_6172_ == 0 {
                    lean_ctor_set(v___x_6171_, 4, v_l_6150_);
                    lean_ctor_set(v___x_6171_, 2, v_v_5917_);
                    lean_ctor_set(v___x_6171_, 1, v_k_5916_);
                    lean_ctor_set(v___x_6171_, 0, v___x_6064_);
                    v___x_6182_ = v___x_6171_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6186_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6186_, 0, v___x_6064_);
                    lean_ctor_set(v_reuseFailAlloc_6186_, 1, v_k_5916_);
                    lean_ctor_set(v_reuseFailAlloc_6186_, 2, v_v_5917_);
                    lean_ctor_set(v_reuseFailAlloc_6186_, 3, v_l_6150_);
                    lean_ctor_set(v_reuseFailAlloc_6186_, 4, v_l_6150_);
                    v___x_6182_ = v_reuseFailAlloc_6186_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_5922_ == 0 {
                    lean_ctor_set(v___x_5921_, 4, v___x_6182_);
                    lean_ctor_set(v___x_5921_, 3, v___x_6180_);
                    lean_ctor_set(v___x_5921_, 2, v_v_6174_);
                    lean_ctor_set(v___x_5921_, 1, v_k_6173_);
                    lean_ctor_set(v___x_5921_, 0, v___x_6178_);
                    v___x_6184_ = v___x_5921_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6185_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6185_, 0, v___x_6178_);
                    lean_ctor_set(v_reuseFailAlloc_6185_, 1, v_k_6173_);
                    lean_ctor_set(v_reuseFailAlloc_6185_, 2, v_v_6174_);
                    lean_ctor_set(v_reuseFailAlloc_6185_, 3, v___x_6180_);
                    lean_ctor_set(v_reuseFailAlloc_6185_, 4, v___x_6182_);
                    v___x_6184_ = v_reuseFailAlloc_6185_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6184_;
            }
            42 => {
                return v___x_6198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
    mut v_k_6203_: *mut LeanObject,
    mut v_t_6204_: *mut LeanObject,
) -> u8 {
    let mut v_k_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: u8 = 0;
    let mut v___x_6209_: u8 = 0;
    let mut v___x_6212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6204_) == 0 {
                    v_k_6205_ = lean_ctor_get(v_t_6204_, 1);
                    v_l_6206_ = lean_ctor_get(v_t_6204_, 3);
                    v_r_6207_ = lean_ctor_get(v_t_6204_, 4);
                    v___x_6208_ = lean_nat_dec_lt(v_k_6203_, v_k_6205_);
                    if v___x_6208_ == 0 {
                        v___x_6209_ = lean_nat_dec_eq(v_k_6203_, v_k_6205_);
                        if v___x_6209_ == 0 {
                            v_t_6204_ = v_r_6207_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_6209_;
                        }
                    } else {
                        v_t_6204_ = v_l_6206_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_6212_ = 0;
                    return v___x_6212_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg___boxed(
    mut v_k_6213_: *mut LeanObject,
    mut v_t_6214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6215_: u8 = 0;
    let mut v_r_6216_: *mut LeanObject = core::ptr::null_mut();
    v_res_6215_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
            v_k_6213_, v_t_6214_,
        );
    lean_dec(v_t_6214_);
    lean_dec(v_k_6213_);
    v_r_6216_ = lean_box((v_res_6215_) as usize);
    return v_r_6216_;
}
pub unsafe fn l_Lean_IR_mkIndexSet(mut v_idx_6217_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: u8 = 0;
    v___x_6218_ = lean_box(1);
    v___x_6219_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
            v_idx_6217_,
            v___x_6218_,
        );
    if v___x_6219_ == 0 {
        let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
        v___x_6220_ = lean_box(0);
        v___x_6221_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
                v_idx_6217_,
                v___x_6220_,
                v___x_6218_,
            );
        return v___x_6221_;
    } else {
        lean_dec(v_idx_6217_);
        return v___x_6218_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(
    mut v_00_u03b2_6222_: *mut LeanObject,
    mut v_k_6223_: *mut LeanObject,
    mut v_t_6224_: *mut LeanObject,
) -> u8 {
    let mut v___x_6225_: u8 = 0;
    v___x_6225_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
            v_k_6223_, v_t_6224_,
        );
    return v___x_6225_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(
    mut v_00_u03b2_6226_: *mut LeanObject,
    mut v_k_6227_: *mut LeanObject,
    mut v_t_6228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6229_: u8 = 0;
    let mut v_r_6230_: *mut LeanObject = core::ptr::null_mut();
    v_res_6229_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(
        v_00_u03b2_6226_,
        v_k_6227_,
        v_t_6228_,
    );
    lean_dec(v_t_6228_);
    lean_dec(v_k_6227_);
    v_r_6230_ = lean_box((v_res_6229_) as usize);
    return v_r_6230_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(
    mut v_00_u03b2_6231_: *mut LeanObject,
    mut v_k_6232_: *mut LeanObject,
    mut v_v_6233_: *mut LeanObject,
    mut v_t_6234_: *mut LeanObject,
    mut v_hl_6235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    v___x_6236_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_k_6232_, v_v_6233_, v_t_6234_,
    );
    return v___x_6236_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorIdx(
    mut v_x_6237_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_6237_) {
        0 => {
            let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
            v___x_6238_ = lean_unsigned_to_nat(0);
            return v___x_6238_;
        }
        1 => {
            let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
            v___x_6239_ = lean_unsigned_to_nat(1);
            return v___x_6239_;
        }
        _ => {
            let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
            v___x_6240_ = lean_unsigned_to_nat(2);
            return v___x_6240_;
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorIdx___boxed(
    mut v_x_6241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6242_: *mut LeanObject = core::ptr::null_mut();
    v_res_6242_ = l_Lean_IR_LocalContextEntry_ctorIdx(v_x_6241_);
    lean_dec_ref(v_x_6241_);
    return v_res_6242_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorElim___redArg(
    mut v_t_6243_: *mut LeanObject,
    mut v_k_6244_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_6243_) {
        0 => {
            let mut v_a_6245_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
            v_a_6245_ = lean_ctor_get(v_t_6243_, 0);
            lean_inc(v_a_6245_);
            lean_dec_ref_known(v_t_6243_, 1);
            v___x_6246_ = lean_apply_1(v_k_6244_, v_a_6245_);
            return v___x_6246_;
        }
        1 => {
            let mut v_a_6247_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_6248_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
            v_a_6247_ = lean_ctor_get(v_t_6243_, 0);
            lean_inc(v_a_6247_);
            v_a_6248_ = lean_ctor_get(v_t_6243_, 1);
            lean_inc_ref(v_a_6248_);
            lean_dec_ref_known(v_t_6243_, 2);
            v___x_6249_ = lean_apply_2(v_k_6244_, v_a_6247_, v_a_6248_);
            return v___x_6249_;
        }
        _ => {
            let mut v_a_6250_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_6251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
            v_a_6250_ = lean_ctor_get(v_t_6243_, 0);
            lean_inc_ref(v_a_6250_);
            v_a_6251_ = lean_ctor_get(v_t_6243_, 1);
            lean_inc(v_a_6251_);
            lean_dec_ref_known(v_t_6243_, 2);
            v___x_6252_ = lean_apply_2(v_k_6244_, v_a_6250_, v_a_6251_);
            return v___x_6252_;
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorElim(
    mut v_motive_6253_: *mut LeanObject,
    mut v_ctorIdx_6254_: *mut LeanObject,
    mut v_t_6255_: *mut LeanObject,
    mut v_h_6256_: *mut LeanObject,
    mut v_k_6257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    v___x_6258_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6255_, v_k_6257_);
    return v___x_6258_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorElim___boxed(
    mut v_motive_6259_: *mut LeanObject,
    mut v_ctorIdx_6260_: *mut LeanObject,
    mut v_t_6261_: *mut LeanObject,
    mut v_h_6262_: *mut LeanObject,
    mut v_k_6263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6264_: *mut LeanObject = core::ptr::null_mut();
    v_res_6264_ = l_Lean_IR_LocalContextEntry_ctorElim(
        v_motive_6259_,
        v_ctorIdx_6260_,
        v_t_6261_,
        v_h_6262_,
        v_k_6263_,
    );
    lean_dec(v_ctorIdx_6260_);
    return v_res_6264_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_param_elim___redArg(
    mut v_t_6265_: *mut LeanObject,
    mut v_param_6266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    v___x_6267_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6265_, v_param_6266_);
    return v___x_6267_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_param_elim(
    mut v_motive_6268_: *mut LeanObject,
    mut v_t_6269_: *mut LeanObject,
    mut v_h_6270_: *mut LeanObject,
    mut v_param_6271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    v___x_6272_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6269_, v_param_6271_);
    return v___x_6272_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_localVar_elim___redArg(
    mut v_t_6273_: *mut LeanObject,
    mut v_localVar_6274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    v___x_6275_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6273_, v_localVar_6274_);
    return v___x_6275_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_localVar_elim(
    mut v_motive_6276_: *mut LeanObject,
    mut v_t_6277_: *mut LeanObject,
    mut v_h_6278_: *mut LeanObject,
    mut v_localVar_6279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    v___x_6280_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6277_, v_localVar_6279_);
    return v___x_6280_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_joinPoint_elim___redArg(
    mut v_t_6281_: *mut LeanObject,
    mut v_joinPoint_6282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6283_: *mut LeanObject = core::ptr::null_mut();
    v___x_6283_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6281_, v_joinPoint_6282_);
    return v___x_6283_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_joinPoint_elim(
    mut v_motive_6284_: *mut LeanObject,
    mut v_t_6285_: *mut LeanObject,
    mut v_h_6286_: *mut LeanObject,
    mut v_joinPoint_6287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    v___x_6288_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6285_, v_joinPoint_6287_);
    return v___x_6288_;
}
pub unsafe fn l_Lean_IR_LocalContext_addLocal(
    mut v_ctx_6289_: *mut LeanObject,
    mut v_x_6290_: *mut LeanObject,
    mut v_t_6291_: *mut LeanObject,
    mut v_v_6292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    v___x_6293_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6293_, 0, v_t_6291_);
    lean_ctor_set(v___x_6293_, 1, v_v_6292_);
    v___x_6294_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_x_6290_,
        v___x_6293_,
        v_ctx_6289_,
    );
    return v___x_6294_;
}
pub unsafe fn l_Lean_IR_LocalContext_addJP(
    mut v_ctx_6295_: *mut LeanObject,
    mut v_j_6296_: *mut LeanObject,
    mut v_xs_6297_: *mut LeanObject,
    mut v_b_6298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    v___x_6299_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_6299_, 0, v_xs_6297_);
    lean_ctor_set(v___x_6299_, 1, v_b_6298_);
    v___x_6300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_j_6296_,
        v___x_6299_,
        v_ctx_6295_,
    );
    return v___x_6300_;
}
pub unsafe fn l_Lean_IR_LocalContext_addParam(
    mut v_ctx_6301_: *mut LeanObject,
    mut v_p_6302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    v_x_6303_ = lean_ctor_get(v_p_6302_, 0);
    lean_inc(v_x_6303_);
    v_ty_6304_ = lean_ctor_get(v_p_6302_, 1);
    lean_inc(v_ty_6304_);
    lean_dec_ref(v_p_6302_);
    v___x_6305_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6305_, 0, v_ty_6304_);
    v___x_6306_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_x_6303_,
        v___x_6305_,
        v_ctx_6301_,
    );
    return v___x_6306_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(
    mut v_as_6307_: *mut LeanObject,
    mut v_i_6308_: usize,
    mut v_stop_6309_: usize,
    mut v_b_6310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6311_: u8 = 0;
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: usize = 0;
    let mut v___x_6315_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6311_ = lean_usize_dec_eq(v_i_6308_, v_stop_6309_);
                if v___x_6311_ == 0 {
                    v___x_6312_ = lean_array_uget_borrowed(v_as_6307_, v_i_6308_);
                    lean_inc(v___x_6312_);
                    v___x_6313_ = l_Lean_IR_LocalContext_addParam(v_b_6310_, v___x_6312_);
                    v___x_6314_ = 1usize;
                    v___x_6315_ = lean_usize_add(v_i_6308_, v___x_6314_);
                    v_i_6308_ = v___x_6315_;
                    v_b_6310_ = v___x_6313_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6310_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0___boxed(
    mut v_as_6317_: *mut LeanObject,
    mut v_i_6318_: *mut LeanObject,
    mut v_stop_6319_: *mut LeanObject,
    mut v_b_6320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6321_: usize = 0;
    let mut v_stop_boxed_6322_: usize = 0;
    let mut v_res_6323_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6321_ = lean_unbox_usize(v_i_6318_);
    lean_dec(v_i_6318_);
    v_stop_boxed_6322_ = lean_unbox_usize(v_stop_6319_);
    lean_dec(v_stop_6319_);
    v_res_6323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_6317_, v_i_boxed_6321_, v_stop_boxed_6322_, v_b_6320_);
    lean_dec_ref(v_as_6317_);
    return v_res_6323_;
}
pub unsafe fn l_Lean_IR_LocalContext_addParams(
    mut v_ctx_6324_: *mut LeanObject,
    mut v_ps_6325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: u8 = 0;
    v___x_6326_ = lean_unsigned_to_nat(0);
    v___x_6327_ = lean_array_get_size(v_ps_6325_);
    v___x_6328_ = lean_nat_dec_lt(v___x_6326_, v___x_6327_);
    if v___x_6328_ == 0 {
        return v_ctx_6324_;
    } else {
        let mut v___x_6329_: u8 = 0;
        v___x_6329_ = lean_nat_dec_le(v___x_6327_, v___x_6327_);
        if v___x_6329_ == 0 {
            if v___x_6328_ == 0 {
                return v_ctx_6324_;
            } else {
                let mut v___x_6330_: usize = 0;
                let mut v___x_6331_: usize = 0;
                let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
                v___x_6330_ = 0usize;
                v___x_6331_ = lean_usize_of_nat(v___x_6327_);
                v___x_6332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_6325_, v___x_6330_, v___x_6331_, v_ctx_6324_);
                return v___x_6332_;
            }
        } else {
            let mut v___x_6333_: usize = 0;
            let mut v___x_6334_: usize = 0;
            let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
            v___x_6333_ = 0usize;
            v___x_6334_ = lean_usize_of_nat(v___x_6327_);
            v___x_6335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_6325_, v___x_6333_, v___x_6334_, v_ctx_6324_);
            return v___x_6335_;
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContext_addParams___boxed(
    mut v_ctx_6336_: *mut LeanObject,
    mut v_ps_6337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6338_: *mut LeanObject = core::ptr::null_mut();
    v_res_6338_ = l_Lean_IR_LocalContext_addParams(v_ctx_6336_, v_ps_6337_);
    lean_dec_ref(v_ps_6337_);
    return v_res_6338_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(
    mut v_t_6339_: *mut LeanObject,
    mut v_k_6340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: u8 = 0;
    let mut v___x_6346_: u8 = 0;
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6339_) == 0 {
                    v_k_6341_ = lean_ctor_get(v_t_6339_, 1);
                    v_v_6342_ = lean_ctor_get(v_t_6339_, 2);
                    v_l_6343_ = lean_ctor_get(v_t_6339_, 3);
                    v_r_6344_ = lean_ctor_get(v_t_6339_, 4);
                    v___x_6345_ = lean_nat_dec_lt(v_k_6340_, v_k_6341_);
                    if v___x_6345_ == 0 {
                        v___x_6346_ = lean_nat_dec_eq(v_k_6340_, v_k_6341_);
                        if v___x_6346_ == 0 {
                            v_t_6339_ = v_r_6344_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc(v_v_6342_);
                            v___x_6348_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_6348_, 0, v_v_6342_);
                            return v___x_6348_;
                        }
                    } else {
                        v_t_6339_ = v_l_6343_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_6350_ = lean_box(0);
                    return v___x_6350_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(
    mut v_t_6351_: *mut LeanObject,
    mut v_k_6352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6353_: *mut LeanObject = core::ptr::null_mut();
    v_res_6353_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_6351_, v_k_6352_);
    lean_dec(v_k_6352_);
    lean_dec(v_t_6351_);
    return v_res_6353_;
}
pub unsafe fn l_Lean_IR_LocalContext_isJP(
    mut v_ctx_6354_: *mut LeanObject,
    mut v_idx_6355_: *mut LeanObject,
) -> u8 {
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    v___x_6356_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6354_, v_idx_6355_);
    if lean_obj_tag(v___x_6356_) == 1 {
        let mut v_val_6357_: *mut LeanObject = core::ptr::null_mut();
        v_val_6357_ = lean_ctor_get(v___x_6356_, 0);
        lean_inc(v_val_6357_);
        lean_dec_ref_known(v___x_6356_, 1);
        if lean_obj_tag(v_val_6357_) == 2 {
            let mut v___x_6358_: u8 = 0;
            lean_dec_ref_known(v_val_6357_, 2);
            v___x_6358_ = 1;
            return v___x_6358_;
        } else {
            let mut v___x_6359_: u8 = 0;
            lean_dec(v_val_6357_);
            v___x_6359_ = 0;
            return v___x_6359_;
        }
    } else {
        let mut v___x_6360_: u8 = 0;
        lean_dec(v___x_6356_);
        v___x_6360_ = 0;
        return v___x_6360_;
    }
}
pub unsafe fn l_Lean_IR_LocalContext_isJP___boxed(
    mut v_ctx_6361_: *mut LeanObject,
    mut v_idx_6362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6363_: u8 = 0;
    let mut v_r_6364_: *mut LeanObject = core::ptr::null_mut();
    v_res_6363_ = l_Lean_IR_LocalContext_isJP(v_ctx_6361_, v_idx_6362_);
    lean_dec(v_idx_6362_);
    lean_dec(v_ctx_6361_);
    v_r_6364_ = lean_box((v_res_6363_) as usize);
    return v_r_6364_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(
    mut v_00_u03b4_6365_: *mut LeanObject,
    mut v_t_6366_: *mut LeanObject,
    mut v_k_6367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    v___x_6368_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_6366_, v_k_6367_);
    return v___x_6368_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___boxed(
    mut v_00_u03b4_6369_: *mut LeanObject,
    mut v_t_6370_: *mut LeanObject,
    mut v_k_6371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6372_: *mut LeanObject = core::ptr::null_mut();
    v_res_6372_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(
            v_00_u03b4_6369_,
            v_t_6370_,
            v_k_6371_,
        );
    lean_dec(v_k_6371_);
    lean_dec(v_t_6370_);
    return v_res_6372_;
}
pub unsafe fn l_Lean_IR_LocalContext_getJPBody(
    mut v_ctx_6373_: *mut LeanObject,
    mut v_j_6374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6379_: u8 = 0;
    let mut v_a_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6385_: u8 = 0;
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6373_, v_j_6374_);
                if lean_obj_tag(v___x_6375_) == 1 {
                    v_val_6376_ = lean_ctor_get(v___x_6375_, 0);
                    v_isSharedCheck_6385_ = (!lean_is_exclusive(v___x_6375_)) as u8;
                    if v_isSharedCheck_6385_ == 0 {
                        v___x_6378_ = v___x_6375_;
                        v_isShared_6379_ = v_isSharedCheck_6385_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6376_);
                        lean_dec(v___x_6375_);
                        v___x_6378_ = lean_box(0);
                        v_isShared_6379_ = v_isSharedCheck_6385_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6375_);
                    v___x_6386_ = lean_box(0);
                    return v___x_6386_;
                }
            }
            1 => {
                if lean_obj_tag(v_val_6376_) == 2 {
                    v_a_6380_ = lean_ctor_get(v_val_6376_, 1);
                    lean_inc(v_a_6380_);
                    lean_dec_ref_known(v_val_6376_, 2);
                    if v_isShared_6379_ == 0 {
                        lean_ctor_set(v___x_6378_, 0, v_a_6380_);
                        v___x_6382_ = v___x_6378_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6383_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_a_6380_);
                        v___x_6382_ = v_reuseFailAlloc_6383_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6378_);
                    lean_dec(v_val_6376_);
                    v___x_6384_ = lean_box(0);
                    return v___x_6384_;
                }
            }
            2 => {
                return v___x_6382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContext_getJPBody___boxed(
    mut v_ctx_6387_: *mut LeanObject,
    mut v_j_6388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6389_: *mut LeanObject = core::ptr::null_mut();
    v_res_6389_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_6387_, v_j_6388_);
    lean_dec(v_j_6388_);
    lean_dec(v_ctx_6387_);
    return v_res_6389_;
}
pub unsafe fn l_Lean_IR_LocalContext_getJPParams(
    mut v_ctx_6390_: *mut LeanObject,
    mut v_j_6391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6396_: u8 = 0;
    let mut v_a_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6402_: u8 = 0;
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6392_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6390_, v_j_6391_);
                if lean_obj_tag(v___x_6392_) == 1 {
                    v_val_6393_ = lean_ctor_get(v___x_6392_, 0);
                    v_isSharedCheck_6402_ = (!lean_is_exclusive(v___x_6392_)) as u8;
                    if v_isSharedCheck_6402_ == 0 {
                        v___x_6395_ = v___x_6392_;
                        v_isShared_6396_ = v_isSharedCheck_6402_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6393_);
                        lean_dec(v___x_6392_);
                        v___x_6395_ = lean_box(0);
                        v_isShared_6396_ = v_isSharedCheck_6402_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6392_);
                    v___x_6403_ = lean_box(0);
                    return v___x_6403_;
                }
            }
            1 => {
                if lean_obj_tag(v_val_6393_) == 2 {
                    v_a_6397_ = lean_ctor_get(v_val_6393_, 0);
                    lean_inc_ref(v_a_6397_);
                    lean_dec_ref_known(v_val_6393_, 2);
                    if v_isShared_6396_ == 0 {
                        lean_ctor_set(v___x_6395_, 0, v_a_6397_);
                        v___x_6399_ = v___x_6395_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6400_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6400_, 0, v_a_6397_);
                        v___x_6399_ = v_reuseFailAlloc_6400_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6395_);
                    lean_dec(v_val_6393_);
                    v___x_6401_ = lean_box(0);
                    return v___x_6401_;
                }
            }
            2 => {
                return v___x_6399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContext_getJPParams___boxed(
    mut v_ctx_6404_: *mut LeanObject,
    mut v_j_6405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6406_: *mut LeanObject = core::ptr::null_mut();
    v_res_6406_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_6404_, v_j_6405_);
    lean_dec(v_j_6405_);
    lean_dec(v_ctx_6404_);
    return v_res_6406_;
}
pub unsafe fn l_Lean_IR_LocalContext_isParam(
    mut v_ctx_6407_: *mut LeanObject,
    mut v_idx_6408_: *mut LeanObject,
) -> u8 {
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    v___x_6409_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6407_, v_idx_6408_);
    if lean_obj_tag(v___x_6409_) == 1 {
        let mut v_val_6410_: *mut LeanObject = core::ptr::null_mut();
        v_val_6410_ = lean_ctor_get(v___x_6409_, 0);
        lean_inc(v_val_6410_);
        lean_dec_ref_known(v___x_6409_, 1);
        if lean_obj_tag(v_val_6410_) == 0 {
            let mut v___x_6411_: u8 = 0;
            lean_dec_ref_known(v_val_6410_, 1);
            v___x_6411_ = 1;
            return v___x_6411_;
        } else {
            let mut v___x_6412_: u8 = 0;
            lean_dec(v_val_6410_);
            v___x_6412_ = 0;
            return v___x_6412_;
        }
    } else {
        let mut v___x_6413_: u8 = 0;
        lean_dec(v___x_6409_);
        v___x_6413_ = 0;
        return v___x_6413_;
    }
}
pub unsafe fn l_Lean_IR_LocalContext_isParam___boxed(
    mut v_ctx_6414_: *mut LeanObject,
    mut v_idx_6415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6416_: u8 = 0;
    let mut v_r_6417_: *mut LeanObject = core::ptr::null_mut();
    v_res_6416_ = l_Lean_IR_LocalContext_isParam(v_ctx_6414_, v_idx_6415_);
    lean_dec(v_idx_6415_);
    lean_dec(v_ctx_6414_);
    v_r_6417_ = lean_box((v_res_6416_) as usize);
    return v_r_6417_;
}
pub unsafe fn l_Lean_IR_LocalContext_isLocalVar(
    mut v_ctx_6418_: *mut LeanObject,
    mut v_idx_6419_: *mut LeanObject,
) -> u8 {
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    v___x_6420_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6418_, v_idx_6419_);
    if lean_obj_tag(v___x_6420_) == 1 {
        let mut v_val_6421_: *mut LeanObject = core::ptr::null_mut();
        v_val_6421_ = lean_ctor_get(v___x_6420_, 0);
        lean_inc(v_val_6421_);
        lean_dec_ref_known(v___x_6420_, 1);
        if lean_obj_tag(v_val_6421_) == 1 {
            let mut v___x_6422_: u8 = 0;
            lean_dec_ref_known(v_val_6421_, 2);
            v___x_6422_ = 1;
            return v___x_6422_;
        } else {
            let mut v___x_6423_: u8 = 0;
            lean_dec(v_val_6421_);
            v___x_6423_ = 0;
            return v___x_6423_;
        }
    } else {
        let mut v___x_6424_: u8 = 0;
        lean_dec(v___x_6420_);
        v___x_6424_ = 0;
        return v___x_6424_;
    }
}
pub unsafe fn l_Lean_IR_LocalContext_isLocalVar___boxed(
    mut v_ctx_6425_: *mut LeanObject,
    mut v_idx_6426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6427_: u8 = 0;
    let mut v_r_6428_: *mut LeanObject = core::ptr::null_mut();
    v_res_6427_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_6425_, v_idx_6426_);
    lean_dec(v_idx_6426_);
    lean_dec(v_ctx_6425_);
    v_r_6428_ = lean_box((v_res_6427_) as usize);
    return v_r_6428_;
}
pub unsafe fn l_Lean_IR_LocalContext_contains(
    mut v_ctx_6429_: *mut LeanObject,
    mut v_idx_6430_: *mut LeanObject,
) -> u8 {
    let mut v___x_6431_: u8 = 0;
    v___x_6431_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
            v_idx_6430_,
            v_ctx_6429_,
        );
    return v___x_6431_;
}
pub unsafe fn l_Lean_IR_LocalContext_contains___boxed(
    mut v_ctx_6432_: *mut LeanObject,
    mut v_idx_6433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6434_: u8 = 0;
    let mut v_r_6435_: *mut LeanObject = core::ptr::null_mut();
    v_res_6434_ = l_Lean_IR_LocalContext_contains(v_ctx_6432_, v_idx_6433_);
    lean_dec(v_idx_6433_);
    lean_dec(v_ctx_6432_);
    v_r_6435_ = lean_box((v_res_6434_) as usize);
    return v_r_6435_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(
    mut v_k_6436_: *mut LeanObject,
    mut v_t_6437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6444_: u8 = 0;
    let mut v___x_6445_: u8 = 0;
    let mut v___x_6446_: u8 = 0;
    let mut v_impl_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: u8 = 0;
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6465_: u8 = 0;
    let mut v_size_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: u8 = 0;
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6477_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6503_: u8 = 0;
    let mut v_unused_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6517_: u8 = 0;
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6521_: u8 = 0;
    let mut v_unused_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_unused_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6546_: u8 = 0;
    let mut v_size_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6556_: u8 = 0;
    let mut v_unused_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6563_: u8 = 0;
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6571_: u8 = 0;
    let mut v_unused_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v_k_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6585_: u8 = 0;
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6596_: u8 = 0;
    let mut v_unused_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6600_: u8 = 0;
    let mut v_unused_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: u8 = 0;
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6625_: u8 = 0;
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: u8 = 0;
    let mut v___x_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6641_: u8 = 0;
    let mut v_size_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: u8 = 0;
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6653_: u8 = 0;
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6678_: u8 = 0;
    let mut v_unused_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6693_: u8 = 0;
    let mut v_unused_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v_k_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6719_: u8 = 0;
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6730_: u8 = 0;
    let mut v_unused_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6752_: u8 = 0;
    let mut v_unused_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_unused_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6766_: u8 = 0;
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tree_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: u8 = 0;
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v_size_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: u8 = 0;
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6794_: u8 = 0;
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6806_: u8 = 0;
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6810_: u8 = 0;
    let mut v_unused_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6829_: u8 = 0;
    let mut v_unused_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut v_unused_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6853_: u8 = 0;
    let mut v_k_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6874_: u8 = 0;
    let mut v_unused_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6882_: u8 = 0;
    let mut v_k_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6889_: u8 = 0;
    let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6900_: u8 = 0;
    let mut v_unused_6901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v_unused_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6916_: u8 = 0;
    let mut v_unused_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: u8 = 0;
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6940_: u8 = 0;
    let mut v_size_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6952_: u8 = 0;
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6977_: u8 = 0;
    let mut v_unused_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6990_: u8 = 0;
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6994_: u8 = 0;
    let mut v_unused_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7001_: u8 = 0;
    let mut v_unused_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7019_: u8 = 0;
    let mut v_size_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7029_: u8 = 0;
    let mut v_unused_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7036_: u8 = 0;
    let mut v_k_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7041_: u8 = 0;
    let mut v___x_7042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7052_: u8 = 0;
    let mut v_unused_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7056_: u8 = 0;
    let mut v_unused_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7065_: u8 = 0;
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7073_: u8 = 0;
    let mut v_unused_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7082_: u8 = 0;
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7090_: u8 = 0;
    let mut v_unused_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7096_: u8 = 0;
    let mut v_unused_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_6437_) == 0 {
                    v_k_6438_ = lean_ctor_get(v_t_6437_, 1);
                    v_v_6439_ = lean_ctor_get(v_t_6437_, 2);
                    v_l_6440_ = lean_ctor_get(v_t_6437_, 3);
                    v_r_6441_ = lean_ctor_get(v_t_6437_, 4);
                    v_isSharedCheck_7096_ = (!lean_is_exclusive(v_t_6437_)) as u8;
                    if v_isSharedCheck_7096_ == 0 {
                        v_unused_7097_ = lean_ctor_get(v_t_6437_, 0);
                        lean_dec(v_unused_7097_);
                        v___x_6443_ = v_t_6437_;
                        v_isShared_6444_ = v_isSharedCheck_7096_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_6441_);
                        lean_inc(v_l_6440_);
                        lean_inc(v_v_6439_);
                        lean_inc(v_k_6438_);
                        lean_dec(v_t_6437_);
                        v___x_6443_ = lean_box(0);
                        v_isShared_6444_ = v_isSharedCheck_7096_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_6437_;
                }
            }
            1 => {
                v___x_6445_ = lean_nat_dec_lt(v_k_6436_, v_k_6438_);
                if v___x_6445_ == 0 {
                    v___x_6446_ = lean_nat_dec_eq(v_k_6436_, v_k_6438_);
                    if v___x_6446_ == 0 {
                        v_impl_6447_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_6436_, v_r_6441_);
                        v___x_6448_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_impl_6447_) == 0 {
                            if lean_obj_tag(v_l_6440_) == 0 {
                                v_size_6449_ = lean_ctor_get(v_impl_6447_, 0);
                                lean_inc(v_size_6449_);
                                v_size_6450_ = lean_ctor_get(v_l_6440_, 0);
                                v_k_6451_ = lean_ctor_get(v_l_6440_, 1);
                                v_v_6452_ = lean_ctor_get(v_l_6440_, 2);
                                v_l_6453_ = lean_ctor_get(v_l_6440_, 3);
                                v_r_6454_ = lean_ctor_get(v_l_6440_, 4);
                                lean_inc(v_r_6454_);
                                v___x_6455_ = lean_unsigned_to_nat(3);
                                v___x_6456_ = lean_nat_mul(v___x_6455_, v_size_6449_);
                                v___x_6457_ = lean_nat_dec_lt(v___x_6456_, v_size_6450_);
                                lean_dec(v___x_6456_);
                                if v___x_6457_ == 0 {
                                    lean_dec(v_r_6454_);
                                    v___x_6458_ = lean_nat_add(v___x_6448_, v_size_6450_);
                                    v___x_6459_ = lean_nat_add(v___x_6458_, v_size_6449_);
                                    lean_dec(v_size_6449_);
                                    lean_dec(v___x_6458_);
                                    if v_isShared_6444_ == 0 {
                                        lean_ctor_set(v___x_6443_, 4, v_impl_6447_);
                                        lean_ctor_set(v___x_6443_, 0, v___x_6459_);
                                        v___x_6461_ = v___x_6443_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6462_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6462_, 0, v___x_6459_);
                                        lean_ctor_set(v_reuseFailAlloc_6462_, 1, v_k_6438_);
                                        lean_ctor_set(v_reuseFailAlloc_6462_, 2, v_v_6439_);
                                        lean_ctor_set(v_reuseFailAlloc_6462_, 3, v_l_6440_);
                                        lean_ctor_set(v_reuseFailAlloc_6462_, 4, v_impl_6447_);
                                        v___x_6461_ = v_reuseFailAlloc_6462_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_l_6453_);
                                    lean_inc(v_v_6452_);
                                    lean_inc(v_k_6451_);
                                    lean_inc(v_size_6450_);
                                    v_isSharedCheck_6528_ = (!lean_is_exclusive(v_l_6440_)) as u8;
                                    if v_isSharedCheck_6528_ == 0 {
                                        v_unused_6529_ = lean_ctor_get(v_l_6440_, 4);
                                        lean_dec(v_unused_6529_);
                                        v_unused_6530_ = lean_ctor_get(v_l_6440_, 3);
                                        lean_dec(v_unused_6530_);
                                        v_unused_6531_ = lean_ctor_get(v_l_6440_, 2);
                                        lean_dec(v_unused_6531_);
                                        v_unused_6532_ = lean_ctor_get(v_l_6440_, 1);
                                        lean_dec(v_unused_6532_);
                                        v_unused_6533_ = lean_ctor_get(v_l_6440_, 0);
                                        lean_dec(v_unused_6533_);
                                        v___x_6464_ = v_l_6440_;
                                        v_isShared_6465_ = v_isSharedCheck_6528_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v_l_6440_);
                                        v___x_6464_ = lean_box(0);
                                        v_isShared_6465_ = v_isSharedCheck_6528_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_6534_ = lean_ctor_get(v_impl_6447_, 0);
                                lean_inc(v_size_6534_);
                                v___x_6535_ = lean_nat_add(v___x_6448_, v_size_6534_);
                                lean_dec(v_size_6534_);
                                if v_isShared_6444_ == 0 {
                                    lean_ctor_set(v___x_6443_, 4, v_impl_6447_);
                                    lean_ctor_set(v___x_6443_, 0, v___x_6535_);
                                    v___x_6537_ = v___x_6443_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6538_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6538_, 0, v___x_6535_);
                                    lean_ctor_set(v_reuseFailAlloc_6538_, 1, v_k_6438_);
                                    lean_ctor_set(v_reuseFailAlloc_6538_, 2, v_v_6439_);
                                    lean_ctor_set(v_reuseFailAlloc_6538_, 3, v_l_6440_);
                                    lean_ctor_set(v_reuseFailAlloc_6538_, 4, v_impl_6447_);
                                    v___x_6537_ = v_reuseFailAlloc_6538_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v_l_6440_) == 0 {
                                v_l_6539_ = lean_ctor_get(v_l_6440_, 3);
                                if lean_obj_tag(v_l_6539_) == 0 {
                                    lean_inc_ref(v_l_6539_);
                                    v_r_6540_ = lean_ctor_get(v_l_6440_, 4);
                                    lean_inc(v_r_6540_);
                                    if lean_obj_tag(v_r_6540_) == 0 {
                                        v_size_6541_ = lean_ctor_get(v_l_6440_, 0);
                                        v_k_6542_ = lean_ctor_get(v_l_6440_, 1);
                                        v_v_6543_ = lean_ctor_get(v_l_6440_, 2);
                                        v_isSharedCheck_6556_ =
                                            (!lean_is_exclusive(v_l_6440_)) as u8;
                                        if v_isSharedCheck_6556_ == 0 {
                                            v_unused_6557_ = lean_ctor_get(v_l_6440_, 4);
                                            lean_dec(v_unused_6557_);
                                            v_unused_6558_ = lean_ctor_get(v_l_6440_, 3);
                                            lean_dec(v_unused_6558_);
                                            v___x_6545_ = v_l_6440_;
                                            v_isShared_6546_ = v_isSharedCheck_6556_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_6543_);
                                            lean_inc(v_k_6542_);
                                            lean_inc(v_size_6541_);
                                            lean_dec(v_l_6440_);
                                            v___x_6545_ = lean_box(0);
                                            v_isShared_6546_ = v_isSharedCheck_6556_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_6559_ = lean_ctor_get(v_l_6440_, 1);
                                        v_v_6560_ = lean_ctor_get(v_l_6440_, 2);
                                        v_isSharedCheck_6571_ =
                                            (!lean_is_exclusive(v_l_6440_)) as u8;
                                        if v_isSharedCheck_6571_ == 0 {
                                            v_unused_6572_ = lean_ctor_get(v_l_6440_, 4);
                                            lean_dec(v_unused_6572_);
                                            v_unused_6573_ = lean_ctor_get(v_l_6440_, 3);
                                            lean_dec(v_unused_6573_);
                                            v_unused_6574_ = lean_ctor_get(v_l_6440_, 0);
                                            lean_dec(v_unused_6574_);
                                            v___x_6562_ = v_l_6440_;
                                            v_isShared_6563_ = v_isSharedCheck_6571_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_6560_);
                                            lean_inc(v_k_6559_);
                                            lean_dec(v_l_6440_);
                                            v___x_6562_ = lean_box(0);
                                            v_isShared_6563_ = v_isSharedCheck_6571_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_6575_ = lean_ctor_get(v_l_6440_, 4);
                                    lean_inc(v_r_6575_);
                                    if lean_obj_tag(v_r_6575_) == 0 {
                                        lean_inc(v_l_6539_);
                                        v_k_6576_ = lean_ctor_get(v_l_6440_, 1);
                                        v_v_6577_ = lean_ctor_get(v_l_6440_, 2);
                                        v_isSharedCheck_6600_ =
                                            (!lean_is_exclusive(v_l_6440_)) as u8;
                                        if v_isSharedCheck_6600_ == 0 {
                                            v_unused_6601_ = lean_ctor_get(v_l_6440_, 4);
                                            lean_dec(v_unused_6601_);
                                            v_unused_6602_ = lean_ctor_get(v_l_6440_, 3);
                                            lean_dec(v_unused_6602_);
                                            v_unused_6603_ = lean_ctor_get(v_l_6440_, 0);
                                            lean_dec(v_unused_6603_);
                                            v___x_6579_ = v_l_6440_;
                                            v_isShared_6580_ = v_isSharedCheck_6600_;
                                            state = 20;
                                            continue;
                                        } else {
                                            lean_inc(v_v_6577_);
                                            lean_inc(v_k_6576_);
                                            lean_dec(v_l_6440_);
                                            v___x_6579_ = lean_box(0);
                                            v_isShared_6580_ = v_isSharedCheck_6600_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_6604_ = lean_unsigned_to_nat(2);
                                        if v_isShared_6444_ == 0 {
                                            lean_ctor_set(v___x_6443_, 4, v_r_6575_);
                                            lean_ctor_set(v___x_6443_, 0, v___x_6604_);
                                            v___x_6606_ = v___x_6443_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_6607_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_6607_, 0, v___x_6604_);
                                            lean_ctor_set(v_reuseFailAlloc_6607_, 1, v_k_6438_);
                                            lean_ctor_set(v_reuseFailAlloc_6607_, 2, v_v_6439_);
                                            lean_ctor_set(v_reuseFailAlloc_6607_, 3, v_l_6440_);
                                            lean_ctor_set(v_reuseFailAlloc_6607_, 4, v_r_6575_);
                                            v___x_6606_ = v_reuseFailAlloc_6607_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_6444_ == 0 {
                                    lean_ctor_set(v___x_6443_, 4, v_l_6440_);
                                    lean_ctor_set(v___x_6443_, 0, v___x_6448_);
                                    v___x_6609_ = v___x_6443_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6610_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6610_, 0, v___x_6448_);
                                    lean_ctor_set(v_reuseFailAlloc_6610_, 1, v_k_6438_);
                                    lean_ctor_set(v_reuseFailAlloc_6610_, 2, v_v_6439_);
                                    lean_ctor_set(v_reuseFailAlloc_6610_, 3, v_l_6440_);
                                    lean_ctor_set(v_reuseFailAlloc_6610_, 4, v_l_6440_);
                                    v___x_6609_ = v_reuseFailAlloc_6610_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_6443_);
                        lean_dec(v_v_6439_);
                        lean_dec(v_k_6438_);
                        if lean_obj_tag(v_l_6440_) == 0 {
                            if lean_obj_tag(v_r_6441_) == 0 {
                                v_size_6611_ = lean_ctor_get(v_l_6440_, 0);
                                v_k_6612_ = lean_ctor_get(v_l_6440_, 1);
                                v_v_6613_ = lean_ctor_get(v_l_6440_, 2);
                                v_l_6614_ = lean_ctor_get(v_l_6440_, 3);
                                v_r_6615_ = lean_ctor_get(v_l_6440_, 4);
                                lean_inc(v_r_6615_);
                                v_size_6616_ = lean_ctor_get(v_r_6441_, 0);
                                v_k_6617_ = lean_ctor_get(v_r_6441_, 1);
                                v_v_6618_ = lean_ctor_get(v_r_6441_, 2);
                                v_l_6619_ = lean_ctor_get(v_r_6441_, 3);
                                lean_inc(v_l_6619_);
                                v_r_6620_ = lean_ctor_get(v_r_6441_, 4);
                                v___x_6621_ = lean_unsigned_to_nat(1);
                                v___x_6622_ = lean_nat_dec_lt(v_size_6611_, v_size_6616_);
                                if v___x_6622_ == 0 {
                                    lean_inc(v_l_6614_);
                                    lean_inc(v_v_6613_);
                                    lean_inc(v_k_6612_);
                                    v_isSharedCheck_6758_ = (!lean_is_exclusive(v_l_6440_)) as u8;
                                    if v_isSharedCheck_6758_ == 0 {
                                        v_unused_6759_ = lean_ctor_get(v_l_6440_, 4);
                                        lean_dec(v_unused_6759_);
                                        v_unused_6760_ = lean_ctor_get(v_l_6440_, 3);
                                        lean_dec(v_unused_6760_);
                                        v_unused_6761_ = lean_ctor_get(v_l_6440_, 2);
                                        lean_dec(v_unused_6761_);
                                        v_unused_6762_ = lean_ctor_get(v_l_6440_, 1);
                                        lean_dec(v_unused_6762_);
                                        v_unused_6763_ = lean_ctor_get(v_l_6440_, 0);
                                        lean_dec(v_unused_6763_);
                                        v___x_6624_ = v_l_6440_;
                                        v_isShared_6625_ = v_isSharedCheck_6758_;
                                        state = 27;
                                        continue;
                                    } else {
                                        lean_dec(v_l_6440_);
                                        v___x_6624_ = lean_box(0);
                                        v_isShared_6625_ = v_isSharedCheck_6758_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_r_6620_);
                                    lean_inc(v_v_6618_);
                                    lean_inc(v_k_6617_);
                                    v_isSharedCheck_6916_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_6916_ == 0 {
                                        v_unused_6917_ = lean_ctor_get(v_r_6441_, 4);
                                        lean_dec(v_unused_6917_);
                                        v_unused_6918_ = lean_ctor_get(v_r_6441_, 3);
                                        lean_dec(v_unused_6918_);
                                        v_unused_6919_ = lean_ctor_get(v_r_6441_, 2);
                                        lean_dec(v_unused_6919_);
                                        v_unused_6920_ = lean_ctor_get(v_r_6441_, 1);
                                        lean_dec(v_unused_6920_);
                                        v_unused_6921_ = lean_ctor_get(v_r_6441_, 0);
                                        lean_dec(v_unused_6921_);
                                        v___x_6765_ = v_r_6441_;
                                        v_isShared_6766_ = v_isSharedCheck_6916_;
                                        state = 49;
                                        continue;
                                    } else {
                                        lean_dec(v_r_6441_);
                                        v___x_6765_ = lean_box(0);
                                        v_isShared_6766_ = v_isSharedCheck_6916_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_6440_;
                            }
                        } else {
                            return v_r_6441_;
                        }
                    }
                } else {
                    v_impl_6922_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_6436_, v_l_6440_);
                    v___x_6923_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_impl_6922_) == 0 {
                        if lean_obj_tag(v_r_6441_) == 0 {
                            v_size_6924_ = lean_ctor_get(v_impl_6922_, 0);
                            lean_inc(v_size_6924_);
                            v_size_6925_ = lean_ctor_get(v_r_6441_, 0);
                            v_k_6926_ = lean_ctor_get(v_r_6441_, 1);
                            v_v_6927_ = lean_ctor_get(v_r_6441_, 2);
                            v_l_6928_ = lean_ctor_get(v_r_6441_, 3);
                            lean_inc(v_l_6928_);
                            v_r_6929_ = lean_ctor_get(v_r_6441_, 4);
                            v___x_6930_ = lean_unsigned_to_nat(3);
                            v___x_6931_ = lean_nat_mul(v___x_6930_, v_size_6924_);
                            v___x_6932_ = lean_nat_dec_lt(v___x_6931_, v_size_6925_);
                            lean_dec(v___x_6931_);
                            if v___x_6932_ == 0 {
                                lean_dec(v_l_6928_);
                                v___x_6933_ = lean_nat_add(v___x_6923_, v_size_6924_);
                                lean_dec(v_size_6924_);
                                v___x_6934_ = lean_nat_add(v___x_6933_, v_size_6925_);
                                lean_dec(v___x_6933_);
                                if v_isShared_6444_ == 0 {
                                    lean_ctor_set(v___x_6443_, 3, v_impl_6922_);
                                    lean_ctor_set(v___x_6443_, 0, v___x_6934_);
                                    v___x_6936_ = v___x_6443_;
                                    state = 72;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6937_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6937_, 0, v___x_6934_);
                                    lean_ctor_set(v_reuseFailAlloc_6937_, 1, v_k_6438_);
                                    lean_ctor_set(v_reuseFailAlloc_6937_, 2, v_v_6439_);
                                    lean_ctor_set(v_reuseFailAlloc_6937_, 3, v_impl_6922_);
                                    lean_ctor_set(v_reuseFailAlloc_6937_, 4, v_r_6441_);
                                    v___x_6936_ = v_reuseFailAlloc_6937_;
                                    state = 72;
                                    continue;
                                }
                            } else {
                                lean_inc(v_r_6929_);
                                lean_inc(v_v_6927_);
                                lean_inc(v_k_6926_);
                                lean_inc(v_size_6925_);
                                v_isSharedCheck_7001_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                                if v_isSharedCheck_7001_ == 0 {
                                    v_unused_7002_ = lean_ctor_get(v_r_6441_, 4);
                                    lean_dec(v_unused_7002_);
                                    v_unused_7003_ = lean_ctor_get(v_r_6441_, 3);
                                    lean_dec(v_unused_7003_);
                                    v_unused_7004_ = lean_ctor_get(v_r_6441_, 2);
                                    lean_dec(v_unused_7004_);
                                    v_unused_7005_ = lean_ctor_get(v_r_6441_, 1);
                                    lean_dec(v_unused_7005_);
                                    v_unused_7006_ = lean_ctor_get(v_r_6441_, 0);
                                    lean_dec(v_unused_7006_);
                                    v___x_6939_ = v_r_6441_;
                                    v_isShared_6940_ = v_isSharedCheck_7001_;
                                    state = 73;
                                    continue;
                                } else {
                                    lean_dec(v_r_6441_);
                                    v___x_6939_ = lean_box(0);
                                    v_isShared_6940_ = v_isSharedCheck_7001_;
                                    state = 73;
                                    continue;
                                }
                            }
                        } else {
                            v_size_7007_ = lean_ctor_get(v_impl_6922_, 0);
                            lean_inc(v_size_7007_);
                            v___x_7008_ = lean_nat_add(v___x_6923_, v_size_7007_);
                            lean_dec(v_size_7007_);
                            if v_isShared_6444_ == 0 {
                                lean_ctor_set(v___x_6443_, 3, v_impl_6922_);
                                lean_ctor_set(v___x_6443_, 0, v___x_7008_);
                                v___x_7010_ = v___x_6443_;
                                state = 83;
                                continue;
                            } else {
                                v_reuseFailAlloc_7011_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7011_, 0, v___x_7008_);
                                lean_ctor_set(v_reuseFailAlloc_7011_, 1, v_k_6438_);
                                lean_ctor_set(v_reuseFailAlloc_7011_, 2, v_v_6439_);
                                lean_ctor_set(v_reuseFailAlloc_7011_, 3, v_impl_6922_);
                                lean_ctor_set(v_reuseFailAlloc_7011_, 4, v_r_6441_);
                                v___x_7010_ = v_reuseFailAlloc_7011_;
                                state = 83;
                                continue;
                            }
                        }
                    } else {
                        if lean_obj_tag(v_r_6441_) == 0 {
                            v_l_7012_ = lean_ctor_get(v_r_6441_, 3);
                            lean_inc(v_l_7012_);
                            if lean_obj_tag(v_l_7012_) == 0 {
                                v_r_7013_ = lean_ctor_get(v_r_6441_, 4);
                                lean_inc(v_r_7013_);
                                if lean_obj_tag(v_r_7013_) == 0 {
                                    v_size_7014_ = lean_ctor_get(v_r_6441_, 0);
                                    v_k_7015_ = lean_ctor_get(v_r_6441_, 1);
                                    v_v_7016_ = lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7029_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7029_ == 0 {
                                        v_unused_7030_ = lean_ctor_get(v_r_6441_, 4);
                                        lean_dec(v_unused_7030_);
                                        v_unused_7031_ = lean_ctor_get(v_r_6441_, 3);
                                        lean_dec(v_unused_7031_);
                                        v___x_7018_ = v_r_6441_;
                                        v_isShared_7019_ = v_isSharedCheck_7029_;
                                        state = 84;
                                        continue;
                                    } else {
                                        lean_inc(v_v_7016_);
                                        lean_inc(v_k_7015_);
                                        lean_inc(v_size_7014_);
                                        lean_dec(v_r_6441_);
                                        v___x_7018_ = lean_box(0);
                                        v_isShared_7019_ = v_isSharedCheck_7029_;
                                        state = 84;
                                        continue;
                                    }
                                } else {
                                    v_k_7032_ = lean_ctor_get(v_r_6441_, 1);
                                    v_v_7033_ = lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7056_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7056_ == 0 {
                                        v_unused_7057_ = lean_ctor_get(v_r_6441_, 4);
                                        lean_dec(v_unused_7057_);
                                        v_unused_7058_ = lean_ctor_get(v_r_6441_, 3);
                                        lean_dec(v_unused_7058_);
                                        v_unused_7059_ = lean_ctor_get(v_r_6441_, 0);
                                        lean_dec(v_unused_7059_);
                                        v___x_7035_ = v_r_6441_;
                                        v_isShared_7036_ = v_isSharedCheck_7056_;
                                        state = 87;
                                        continue;
                                    } else {
                                        lean_inc(v_v_7033_);
                                        lean_inc(v_k_7032_);
                                        lean_dec(v_r_6441_);
                                        v___x_7035_ = lean_box(0);
                                        v_isShared_7036_ = v_isSharedCheck_7056_;
                                        state = 87;
                                        continue;
                                    }
                                }
                            } else {
                                v_r_7060_ = lean_ctor_get(v_r_6441_, 4);
                                lean_inc(v_r_7060_);
                                if lean_obj_tag(v_r_7060_) == 0 {
                                    v_k_7061_ = lean_ctor_get(v_r_6441_, 1);
                                    v_v_7062_ = lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7073_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7073_ == 0 {
                                        v_unused_7074_ = lean_ctor_get(v_r_6441_, 4);
                                        lean_dec(v_unused_7074_);
                                        v_unused_7075_ = lean_ctor_get(v_r_6441_, 3);
                                        lean_dec(v_unused_7075_);
                                        v_unused_7076_ = lean_ctor_get(v_r_6441_, 0);
                                        lean_dec(v_unused_7076_);
                                        v___x_7064_ = v_r_6441_;
                                        v_isShared_7065_ = v_isSharedCheck_7073_;
                                        state = 92;
                                        continue;
                                    } else {
                                        lean_inc(v_v_7062_);
                                        lean_inc(v_k_7061_);
                                        lean_dec(v_r_6441_);
                                        v___x_7064_ = lean_box(0);
                                        v_isShared_7065_ = v_isSharedCheck_7073_;
                                        state = 92;
                                        continue;
                                    }
                                } else {
                                    v_size_7077_ = lean_ctor_get(v_r_6441_, 0);
                                    v_k_7078_ = lean_ctor_get(v_r_6441_, 1);
                                    v_v_7079_ = lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7090_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7090_ == 0 {
                                        v_unused_7091_ = lean_ctor_get(v_r_6441_, 4);
                                        lean_dec(v_unused_7091_);
                                        v_unused_7092_ = lean_ctor_get(v_r_6441_, 3);
                                        lean_dec(v_unused_7092_);
                                        v___x_7081_ = v_r_6441_;
                                        v_isShared_7082_ = v_isSharedCheck_7090_;
                                        state = 95;
                                        continue;
                                    } else {
                                        lean_inc(v_v_7079_);
                                        lean_inc(v_k_7078_);
                                        lean_inc(v_size_7077_);
                                        lean_dec(v_r_6441_);
                                        v___x_7081_ = lean_box(0);
                                        v_isShared_7082_ = v_isSharedCheck_7090_;
                                        state = 95;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            if v_isShared_6444_ == 0 {
                                lean_ctor_set(v___x_6443_, 3, v_r_6441_);
                                lean_ctor_set(v___x_6443_, 0, v___x_6923_);
                                v___x_7094_ = v___x_6443_;
                                state = 98;
                                continue;
                            } else {
                                v_reuseFailAlloc_7095_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7095_, 0, v___x_6923_);
                                lean_ctor_set(v_reuseFailAlloc_7095_, 1, v_k_6438_);
                                lean_ctor_set(v_reuseFailAlloc_7095_, 2, v_v_6439_);
                                lean_ctor_set(v_reuseFailAlloc_7095_, 3, v_r_6441_);
                                lean_ctor_set(v_reuseFailAlloc_7095_, 4, v_r_6441_);
                                v___x_7094_ = v_reuseFailAlloc_7095_;
                                state = 98;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_6461_;
            }
            3 => {
                v_size_6466_ = lean_ctor_get(v_l_6453_, 0);
                v_size_6467_ = lean_ctor_get(v_r_6454_, 0);
                v_k_6468_ = lean_ctor_get(v_r_6454_, 1);
                v_v_6469_ = lean_ctor_get(v_r_6454_, 2);
                v_l_6470_ = lean_ctor_get(v_r_6454_, 3);
                v_r_6471_ = lean_ctor_get(v_r_6454_, 4);
                v___x_6472_ = lean_unsigned_to_nat(2);
                v___x_6473_ = lean_nat_mul(v___x_6472_, v_size_6466_);
                v___x_6474_ = lean_nat_dec_lt(v_size_6467_, v___x_6473_);
                lean_dec(v___x_6473_);
                if v___x_6474_ == 0 {
                    lean_inc(v_r_6471_);
                    lean_inc(v_l_6470_);
                    lean_inc(v_v_6469_);
                    lean_inc(v_k_6468_);
                    v_isSharedCheck_6503_ = (!lean_is_exclusive(v_r_6454_)) as u8;
                    if v_isSharedCheck_6503_ == 0 {
                        v_unused_6504_ = lean_ctor_get(v_r_6454_, 4);
                        lean_dec(v_unused_6504_);
                        v_unused_6505_ = lean_ctor_get(v_r_6454_, 3);
                        lean_dec(v_unused_6505_);
                        v_unused_6506_ = lean_ctor_get(v_r_6454_, 2);
                        lean_dec(v_unused_6506_);
                        v_unused_6507_ = lean_ctor_get(v_r_6454_, 1);
                        lean_dec(v_unused_6507_);
                        v_unused_6508_ = lean_ctor_get(v_r_6454_, 0);
                        lean_dec(v_unused_6508_);
                        v___x_6476_ = v_r_6454_;
                        v_isShared_6477_ = v_isSharedCheck_6503_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_6454_);
                        v___x_6476_ = lean_box(0);
                        v_isShared_6477_ = v_isSharedCheck_6503_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6443_);
                    v___x_6509_ = lean_nat_add(v___x_6448_, v_size_6450_);
                    lean_dec(v_size_6450_);
                    v___x_6510_ = lean_nat_add(v___x_6509_, v_size_6449_);
                    lean_dec(v___x_6509_);
                    v___x_6511_ = lean_nat_add(v___x_6448_, v_size_6449_);
                    lean_dec(v_size_6449_);
                    v___x_6512_ = lean_nat_add(v___x_6511_, v_size_6467_);
                    lean_dec(v___x_6511_);
                    lean_inc_ref(v_impl_6447_);
                    if v_isShared_6465_ == 0 {
                        lean_ctor_set(v___x_6464_, 4, v_impl_6447_);
                        lean_ctor_set(v___x_6464_, 3, v_r_6454_);
                        lean_ctor_set(v___x_6464_, 2, v_v_6439_);
                        lean_ctor_set(v___x_6464_, 1, v_k_6438_);
                        lean_ctor_set(v___x_6464_, 0, v___x_6512_);
                        v___x_6514_ = v___x_6464_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6527_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6527_, 0, v___x_6512_);
                        lean_ctor_set(v_reuseFailAlloc_6527_, 1, v_k_6438_);
                        lean_ctor_set(v_reuseFailAlloc_6527_, 2, v_v_6439_);
                        lean_ctor_set(v_reuseFailAlloc_6527_, 3, v_r_6454_);
                        lean_ctor_set(v_reuseFailAlloc_6527_, 4, v_impl_6447_);
                        v___x_6514_ = v_reuseFailAlloc_6527_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6478_ = lean_nat_add(v___x_6448_, v_size_6450_);
                lean_dec(v_size_6450_);
                v___x_6479_ = lean_nat_add(v___x_6478_, v_size_6449_);
                lean_dec(v___x_6478_);
                v___x_6491_ = lean_nat_add(v___x_6448_, v_size_6466_);
                if lean_obj_tag(v_l_6470_) == 0 {
                    v_size_6501_ = lean_ctor_get(v_l_6470_, 0);
                    lean_inc(v_size_6501_);
                    v___y_6493_ = v_size_6501_;
                    state = 8;
                    continue;
                } else {
                    v___x_6502_ = lean_unsigned_to_nat(0);
                    v___y_6493_ = v___x_6502_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_6484_ = lean_nat_add(v___y_6481_, v___y_6483_);
                lean_dec(v___y_6483_);
                lean_dec(v___y_6481_);
                if v_isShared_6477_ == 0 {
                    lean_ctor_set(v___x_6476_, 4, v_impl_6447_);
                    lean_ctor_set(v___x_6476_, 3, v_r_6471_);
                    lean_ctor_set(v___x_6476_, 2, v_v_6439_);
                    lean_ctor_set(v___x_6476_, 1, v_k_6438_);
                    lean_ctor_set(v___x_6476_, 0, v___x_6484_);
                    v___x_6486_ = v___x_6476_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6490_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 0, v___x_6484_);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 3, v_r_6471_);
                    lean_ctor_set(v_reuseFailAlloc_6490_, 4, v_impl_6447_);
                    v___x_6486_ = v_reuseFailAlloc_6490_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6465_ == 0 {
                    lean_ctor_set(v___x_6464_, 4, v___x_6486_);
                    lean_ctor_set(v___x_6464_, 3, v___y_6482_);
                    lean_ctor_set(v___x_6464_, 2, v_v_6469_);
                    lean_ctor_set(v___x_6464_, 1, v_k_6468_);
                    lean_ctor_set(v___x_6464_, 0, v___x_6479_);
                    v___x_6488_ = v___x_6464_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6489_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6489_, 0, v___x_6479_);
                    lean_ctor_set(v_reuseFailAlloc_6489_, 1, v_k_6468_);
                    lean_ctor_set(v_reuseFailAlloc_6489_, 2, v_v_6469_);
                    lean_ctor_set(v_reuseFailAlloc_6489_, 3, v___y_6482_);
                    lean_ctor_set(v_reuseFailAlloc_6489_, 4, v___x_6486_);
                    v___x_6488_ = v_reuseFailAlloc_6489_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6488_;
            }
            8 => {
                v___x_6494_ = lean_nat_add(v___x_6491_, v___y_6493_);
                lean_dec(v___y_6493_);
                lean_dec(v___x_6491_);
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v_l_6470_);
                    lean_ctor_set(v___x_6443_, 3, v_l_6453_);
                    lean_ctor_set(v___x_6443_, 2, v_v_6452_);
                    lean_ctor_set(v___x_6443_, 1, v_k_6451_);
                    lean_ctor_set(v___x_6443_, 0, v___x_6494_);
                    v___x_6496_ = v___x_6443_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6500_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6500_, 0, v___x_6494_);
                    lean_ctor_set(v_reuseFailAlloc_6500_, 1, v_k_6451_);
                    lean_ctor_set(v_reuseFailAlloc_6500_, 2, v_v_6452_);
                    lean_ctor_set(v_reuseFailAlloc_6500_, 3, v_l_6453_);
                    lean_ctor_set(v_reuseFailAlloc_6500_, 4, v_l_6470_);
                    v___x_6496_ = v_reuseFailAlloc_6500_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6497_ = lean_nat_add(v___x_6448_, v_size_6449_);
                lean_dec(v_size_6449_);
                if lean_obj_tag(v_r_6471_) == 0 {
                    v_size_6498_ = lean_ctor_get(v_r_6471_, 0);
                    lean_inc(v_size_6498_);
                    v___y_6481_ = v___x_6497_;
                    v___y_6482_ = v___x_6496_;
                    v___y_6483_ = v_size_6498_;
                    state = 5;
                    continue;
                } else {
                    v___x_6499_ = lean_unsigned_to_nat(0);
                    v___y_6481_ = v___x_6497_;
                    v___y_6482_ = v___x_6496_;
                    v___y_6483_ = v___x_6499_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_6521_ = (!lean_is_exclusive(v_impl_6447_)) as u8;
                if v_isSharedCheck_6521_ == 0 {
                    v_unused_6522_ = lean_ctor_get(v_impl_6447_, 4);
                    lean_dec(v_unused_6522_);
                    v_unused_6523_ = lean_ctor_get(v_impl_6447_, 3);
                    lean_dec(v_unused_6523_);
                    v_unused_6524_ = lean_ctor_get(v_impl_6447_, 2);
                    lean_dec(v_unused_6524_);
                    v_unused_6525_ = lean_ctor_get(v_impl_6447_, 1);
                    lean_dec(v_unused_6525_);
                    v_unused_6526_ = lean_ctor_get(v_impl_6447_, 0);
                    lean_dec(v_unused_6526_);
                    v___x_6516_ = v_impl_6447_;
                    v_isShared_6517_ = v_isSharedCheck_6521_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_impl_6447_);
                    v___x_6516_ = lean_box(0);
                    v_isShared_6517_ = v_isSharedCheck_6521_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_6517_ == 0 {
                    lean_ctor_set(v___x_6516_, 4, v___x_6514_);
                    lean_ctor_set(v___x_6516_, 3, v_l_6453_);
                    lean_ctor_set(v___x_6516_, 2, v_v_6452_);
                    lean_ctor_set(v___x_6516_, 1, v_k_6451_);
                    lean_ctor_set(v___x_6516_, 0, v___x_6510_);
                    v___x_6519_ = v___x_6516_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6520_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6520_, 0, v___x_6510_);
                    lean_ctor_set(v_reuseFailAlloc_6520_, 1, v_k_6451_);
                    lean_ctor_set(v_reuseFailAlloc_6520_, 2, v_v_6452_);
                    lean_ctor_set(v_reuseFailAlloc_6520_, 3, v_l_6453_);
                    lean_ctor_set(v_reuseFailAlloc_6520_, 4, v___x_6514_);
                    v___x_6519_ = v_reuseFailAlloc_6520_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6519_;
            }
            13 => {
                return v___x_6537_;
            }
            14 => {
                v_size_6547_ = lean_ctor_get(v_r_6540_, 0);
                v___x_6548_ = lean_nat_add(v___x_6448_, v_size_6541_);
                lean_dec(v_size_6541_);
                v___x_6549_ = lean_nat_add(v___x_6448_, v_size_6547_);
                if v_isShared_6546_ == 0 {
                    lean_ctor_set(v___x_6545_, 4, v_impl_6447_);
                    lean_ctor_set(v___x_6545_, 3, v_r_6540_);
                    lean_ctor_set(v___x_6545_, 2, v_v_6439_);
                    lean_ctor_set(v___x_6545_, 1, v_k_6438_);
                    lean_ctor_set(v___x_6545_, 0, v___x_6549_);
                    v___x_6551_ = v___x_6545_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6555_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6555_, 0, v___x_6549_);
                    lean_ctor_set(v_reuseFailAlloc_6555_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_6555_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_6555_, 3, v_r_6540_);
                    lean_ctor_set(v_reuseFailAlloc_6555_, 4, v_impl_6447_);
                    v___x_6551_ = v_reuseFailAlloc_6555_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v___x_6551_);
                    lean_ctor_set(v___x_6443_, 3, v_l_6539_);
                    lean_ctor_set(v___x_6443_, 2, v_v_6543_);
                    lean_ctor_set(v___x_6443_, 1, v_k_6542_);
                    lean_ctor_set(v___x_6443_, 0, v___x_6548_);
                    v___x_6553_ = v___x_6443_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6554_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6554_, 0, v___x_6548_);
                    lean_ctor_set(v_reuseFailAlloc_6554_, 1, v_k_6542_);
                    lean_ctor_set(v_reuseFailAlloc_6554_, 2, v_v_6543_);
                    lean_ctor_set(v_reuseFailAlloc_6554_, 3, v_l_6539_);
                    lean_ctor_set(v_reuseFailAlloc_6554_, 4, v___x_6551_);
                    v___x_6553_ = v_reuseFailAlloc_6554_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6553_;
            }
            17 => {
                v___x_6564_ = lean_unsigned_to_nat(3);
                if v_isShared_6563_ == 0 {
                    lean_ctor_set(v___x_6562_, 3, v_r_6540_);
                    lean_ctor_set(v___x_6562_, 2, v_v_6439_);
                    lean_ctor_set(v___x_6562_, 1, v_k_6438_);
                    lean_ctor_set(v___x_6562_, 0, v___x_6448_);
                    v___x_6566_ = v___x_6562_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6570_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6570_, 0, v___x_6448_);
                    lean_ctor_set(v_reuseFailAlloc_6570_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_6570_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_6570_, 3, v_r_6540_);
                    lean_ctor_set(v_reuseFailAlloc_6570_, 4, v_r_6540_);
                    v___x_6566_ = v_reuseFailAlloc_6570_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v___x_6566_);
                    lean_ctor_set(v___x_6443_, 3, v_l_6539_);
                    lean_ctor_set(v___x_6443_, 2, v_v_6560_);
                    lean_ctor_set(v___x_6443_, 1, v_k_6559_);
                    lean_ctor_set(v___x_6443_, 0, v___x_6564_);
                    v___x_6568_ = v___x_6443_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6569_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6569_, 0, v___x_6564_);
                    lean_ctor_set(v_reuseFailAlloc_6569_, 1, v_k_6559_);
                    lean_ctor_set(v_reuseFailAlloc_6569_, 2, v_v_6560_);
                    lean_ctor_set(v_reuseFailAlloc_6569_, 3, v_l_6539_);
                    lean_ctor_set(v_reuseFailAlloc_6569_, 4, v___x_6566_);
                    v___x_6568_ = v_reuseFailAlloc_6569_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6568_;
            }
            20 => {
                v_k_6581_ = lean_ctor_get(v_r_6575_, 1);
                v_v_6582_ = lean_ctor_get(v_r_6575_, 2);
                v_isSharedCheck_6596_ = (!lean_is_exclusive(v_r_6575_)) as u8;
                if v_isSharedCheck_6596_ == 0 {
                    v_unused_6597_ = lean_ctor_get(v_r_6575_, 4);
                    lean_dec(v_unused_6597_);
                    v_unused_6598_ = lean_ctor_get(v_r_6575_, 3);
                    lean_dec(v_unused_6598_);
                    v_unused_6599_ = lean_ctor_get(v_r_6575_, 0);
                    lean_dec(v_unused_6599_);
                    v___x_6584_ = v_r_6575_;
                    v_isShared_6585_ = v_isSharedCheck_6596_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_v_6582_);
                    lean_inc(v_k_6581_);
                    lean_dec(v_r_6575_);
                    v___x_6584_ = lean_box(0);
                    v_isShared_6585_ = v_isSharedCheck_6596_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_6586_ = lean_unsigned_to_nat(3);
                if v_isShared_6585_ == 0 {
                    lean_ctor_set(v___x_6584_, 4, v_l_6539_);
                    lean_ctor_set(v___x_6584_, 3, v_l_6539_);
                    lean_ctor_set(v___x_6584_, 2, v_v_6577_);
                    lean_ctor_set(v___x_6584_, 1, v_k_6576_);
                    lean_ctor_set(v___x_6584_, 0, v___x_6448_);
                    v___x_6588_ = v___x_6584_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6595_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 0, v___x_6448_);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 1, v_k_6576_);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 2, v_v_6577_);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 3, v_l_6539_);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 4, v_l_6539_);
                    v___x_6588_ = v_reuseFailAlloc_6595_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_6580_ == 0 {
                    lean_ctor_set(v___x_6579_, 4, v_l_6539_);
                    lean_ctor_set(v___x_6579_, 2, v_v_6439_);
                    lean_ctor_set(v___x_6579_, 1, v_k_6438_);
                    lean_ctor_set(v___x_6579_, 0, v___x_6448_);
                    v___x_6590_ = v___x_6579_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 0, v___x_6448_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 3, v_l_6539_);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 4, v_l_6539_);
                    v___x_6590_ = v_reuseFailAlloc_6594_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v___x_6590_);
                    lean_ctor_set(v___x_6443_, 3, v___x_6588_);
                    lean_ctor_set(v___x_6443_, 2, v_v_6582_);
                    lean_ctor_set(v___x_6443_, 1, v_k_6581_);
                    lean_ctor_set(v___x_6443_, 0, v___x_6586_);
                    v___x_6592_ = v___x_6443_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6593_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 0, v___x_6586_);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 1, v_k_6581_);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 2, v_v_6582_);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 3, v___x_6588_);
                    lean_ctor_set(v_reuseFailAlloc_6593_, 4, v___x_6590_);
                    v___x_6592_ = v_reuseFailAlloc_6593_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6592_;
            }
            25 => {
                return v___x_6606_;
            }
            26 => {
                return v___x_6609_;
            }
            27 => {
                v___x_6626_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_6612_, v_v_6613_, v_l_6614_, v_r_6615_,
                );
                v_tree_6627_ = lean_ctor_get(v___x_6626_, 2);
                lean_inc(v_tree_6627_);
                if lean_obj_tag(v_tree_6627_) == 0 {
                    v_k_6628_ = lean_ctor_get(v___x_6626_, 0);
                    lean_inc(v_k_6628_);
                    v_v_6629_ = lean_ctor_get(v___x_6626_, 1);
                    lean_inc(v_v_6629_);
                    lean_dec_ref(v___x_6626_);
                    v_size_6630_ = lean_ctor_get(v_tree_6627_, 0);
                    v___x_6631_ = lean_unsigned_to_nat(3);
                    v___x_6632_ = lean_nat_mul(v___x_6631_, v_size_6630_);
                    v___x_6633_ = lean_nat_dec_lt(v___x_6632_, v_size_6616_);
                    lean_dec(v___x_6632_);
                    if v___x_6633_ == 0 {
                        lean_dec(v_l_6619_);
                        v___x_6634_ = lean_nat_add(v___x_6621_, v_size_6630_);
                        v___x_6635_ = lean_nat_add(v___x_6634_, v_size_6616_);
                        lean_dec(v___x_6634_);
                        if v_isShared_6625_ == 0 {
                            lean_ctor_set(v___x_6624_, 4, v_r_6441_);
                            lean_ctor_set(v___x_6624_, 3, v_tree_6627_);
                            lean_ctor_set(v___x_6624_, 2, v_v_6629_);
                            lean_ctor_set(v___x_6624_, 1, v_k_6628_);
                            lean_ctor_set(v___x_6624_, 0, v___x_6635_);
                            v___x_6637_ = v___x_6624_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_6638_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6638_, 0, v___x_6635_);
                            lean_ctor_set(v_reuseFailAlloc_6638_, 1, v_k_6628_);
                            lean_ctor_set(v_reuseFailAlloc_6638_, 2, v_v_6629_);
                            lean_ctor_set(v_reuseFailAlloc_6638_, 3, v_tree_6627_);
                            lean_ctor_set(v_reuseFailAlloc_6638_, 4, v_r_6441_);
                            v___x_6637_ = v_reuseFailAlloc_6638_;
                            state = 28;
                            continue;
                        }
                    } else {
                        lean_inc(v_r_6620_);
                        lean_inc(v_v_6618_);
                        lean_inc(v_k_6617_);
                        lean_inc(v_size_6616_);
                        v_isSharedCheck_6693_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                        if v_isSharedCheck_6693_ == 0 {
                            v_unused_6694_ = lean_ctor_get(v_r_6441_, 4);
                            lean_dec(v_unused_6694_);
                            v_unused_6695_ = lean_ctor_get(v_r_6441_, 3);
                            lean_dec(v_unused_6695_);
                            v_unused_6696_ = lean_ctor_get(v_r_6441_, 2);
                            lean_dec(v_unused_6696_);
                            v_unused_6697_ = lean_ctor_get(v_r_6441_, 1);
                            lean_dec(v_unused_6697_);
                            v_unused_6698_ = lean_ctor_get(v_r_6441_, 0);
                            lean_dec(v_unused_6698_);
                            v___x_6640_ = v_r_6441_;
                            v_isShared_6641_ = v_isSharedCheck_6693_;
                            state = 29;
                            continue;
                        } else {
                            lean_dec(v_r_6441_);
                            v___x_6640_ = lean_box(0);
                            v_isShared_6641_ = v_isSharedCheck_6693_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_r_6620_);
                    lean_inc(v_v_6618_);
                    lean_inc(v_k_6617_);
                    lean_inc(v_size_6616_);
                    v_isSharedCheck_6752_ = (!lean_is_exclusive(v_r_6441_)) as u8;
                    if v_isSharedCheck_6752_ == 0 {
                        v_unused_6753_ = lean_ctor_get(v_r_6441_, 4);
                        lean_dec(v_unused_6753_);
                        v_unused_6754_ = lean_ctor_get(v_r_6441_, 3);
                        lean_dec(v_unused_6754_);
                        v_unused_6755_ = lean_ctor_get(v_r_6441_, 2);
                        lean_dec(v_unused_6755_);
                        v_unused_6756_ = lean_ctor_get(v_r_6441_, 1);
                        lean_dec(v_unused_6756_);
                        v_unused_6757_ = lean_ctor_get(v_r_6441_, 0);
                        lean_dec(v_unused_6757_);
                        v___x_6700_ = v_r_6441_;
                        v_isShared_6701_ = v_isSharedCheck_6752_;
                        state = 38;
                        continue;
                    } else {
                        lean_dec(v_r_6441_);
                        v___x_6700_ = lean_box(0);
                        v_isShared_6701_ = v_isSharedCheck_6752_;
                        state = 38;
                        continue;
                    }
                }
            }
            28 => {
                return v___x_6637_;
            }
            29 => {
                v_size_6642_ = lean_ctor_get(v_l_6619_, 0);
                v_k_6643_ = lean_ctor_get(v_l_6619_, 1);
                v_v_6644_ = lean_ctor_get(v_l_6619_, 2);
                v_l_6645_ = lean_ctor_get(v_l_6619_, 3);
                v_r_6646_ = lean_ctor_get(v_l_6619_, 4);
                v_size_6647_ = lean_ctor_get(v_r_6620_, 0);
                v___x_6648_ = lean_unsigned_to_nat(2);
                v___x_6649_ = lean_nat_mul(v___x_6648_, v_size_6647_);
                v___x_6650_ = lean_nat_dec_lt(v_size_6642_, v___x_6649_);
                lean_dec(v___x_6649_);
                if v___x_6650_ == 0 {
                    lean_inc(v_r_6646_);
                    lean_inc(v_l_6645_);
                    lean_inc(v_v_6644_);
                    lean_inc(v_k_6643_);
                    v_isSharedCheck_6678_ = (!lean_is_exclusive(v_l_6619_)) as u8;
                    if v_isSharedCheck_6678_ == 0 {
                        v_unused_6679_ = lean_ctor_get(v_l_6619_, 4);
                        lean_dec(v_unused_6679_);
                        v_unused_6680_ = lean_ctor_get(v_l_6619_, 3);
                        lean_dec(v_unused_6680_);
                        v_unused_6681_ = lean_ctor_get(v_l_6619_, 2);
                        lean_dec(v_unused_6681_);
                        v_unused_6682_ = lean_ctor_get(v_l_6619_, 1);
                        lean_dec(v_unused_6682_);
                        v_unused_6683_ = lean_ctor_get(v_l_6619_, 0);
                        lean_dec(v_unused_6683_);
                        v___x_6652_ = v_l_6619_;
                        v_isShared_6653_ = v_isSharedCheck_6678_;
                        state = 30;
                        continue;
                    } else {
                        lean_dec(v_l_6619_);
                        v___x_6652_ = lean_box(0);
                        v_isShared_6653_ = v_isSharedCheck_6678_;
                        state = 30;
                        continue;
                    }
                } else {
                    v___x_6684_ = lean_nat_add(v___x_6621_, v_size_6630_);
                    v___x_6685_ = lean_nat_add(v___x_6684_, v_size_6616_);
                    lean_dec(v_size_6616_);
                    v___x_6686_ = lean_nat_add(v___x_6684_, v_size_6642_);
                    lean_dec(v___x_6684_);
                    if v_isShared_6641_ == 0 {
                        lean_ctor_set(v___x_6640_, 4, v_l_6619_);
                        lean_ctor_set(v___x_6640_, 3, v_tree_6627_);
                        lean_ctor_set(v___x_6640_, 2, v_v_6629_);
                        lean_ctor_set(v___x_6640_, 1, v_k_6628_);
                        lean_ctor_set(v___x_6640_, 0, v___x_6686_);
                        v___x_6688_ = v___x_6640_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_6692_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6692_, 0, v___x_6686_);
                        lean_ctor_set(v_reuseFailAlloc_6692_, 1, v_k_6628_);
                        lean_ctor_set(v_reuseFailAlloc_6692_, 2, v_v_6629_);
                        lean_ctor_set(v_reuseFailAlloc_6692_, 3, v_tree_6627_);
                        lean_ctor_set(v_reuseFailAlloc_6692_, 4, v_l_6619_);
                        v___x_6688_ = v_reuseFailAlloc_6692_;
                        state = 36;
                        continue;
                    }
                }
            }
            30 => {
                v___x_6654_ = lean_nat_add(v___x_6621_, v_size_6630_);
                v___x_6655_ = lean_nat_add(v___x_6654_, v_size_6616_);
                lean_dec(v_size_6616_);
                if lean_obj_tag(v_l_6645_) == 0 {
                    v_size_6676_ = lean_ctor_get(v_l_6645_, 0);
                    lean_inc(v_size_6676_);
                    v___y_6668_ = v_size_6676_;
                    state = 34;
                    continue;
                } else {
                    v___x_6677_ = lean_unsigned_to_nat(0);
                    v___y_6668_ = v___x_6677_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_6660_ = lean_nat_add(v___y_6658_, v___y_6659_);
                lean_dec(v___y_6659_);
                lean_dec(v___y_6658_);
                if v_isShared_6653_ == 0 {
                    lean_ctor_set(v___x_6652_, 4, v_r_6620_);
                    lean_ctor_set(v___x_6652_, 3, v_r_6646_);
                    lean_ctor_set(v___x_6652_, 2, v_v_6618_);
                    lean_ctor_set(v___x_6652_, 1, v_k_6617_);
                    lean_ctor_set(v___x_6652_, 0, v___x_6660_);
                    v___x_6662_ = v___x_6652_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6666_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6666_, 0, v___x_6660_);
                    lean_ctor_set(v_reuseFailAlloc_6666_, 1, v_k_6617_);
                    lean_ctor_set(v_reuseFailAlloc_6666_, 2, v_v_6618_);
                    lean_ctor_set(v_reuseFailAlloc_6666_, 3, v_r_6646_);
                    lean_ctor_set(v_reuseFailAlloc_6666_, 4, v_r_6620_);
                    v___x_6662_ = v_reuseFailAlloc_6666_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_6641_ == 0 {
                    lean_ctor_set(v___x_6640_, 4, v___x_6662_);
                    lean_ctor_set(v___x_6640_, 3, v___y_6657_);
                    lean_ctor_set(v___x_6640_, 2, v_v_6644_);
                    lean_ctor_set(v___x_6640_, 1, v_k_6643_);
                    lean_ctor_set(v___x_6640_, 0, v___x_6655_);
                    v___x_6664_ = v___x_6640_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6665_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6665_, 0, v___x_6655_);
                    lean_ctor_set(v_reuseFailAlloc_6665_, 1, v_k_6643_);
                    lean_ctor_set(v_reuseFailAlloc_6665_, 2, v_v_6644_);
                    lean_ctor_set(v_reuseFailAlloc_6665_, 3, v___y_6657_);
                    lean_ctor_set(v_reuseFailAlloc_6665_, 4, v___x_6662_);
                    v___x_6664_ = v_reuseFailAlloc_6665_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6664_;
            }
            34 => {
                v___x_6669_ = lean_nat_add(v___x_6654_, v___y_6668_);
                lean_dec(v___y_6668_);
                lean_dec(v___x_6654_);
                if v_isShared_6625_ == 0 {
                    lean_ctor_set(v___x_6624_, 4, v_l_6645_);
                    lean_ctor_set(v___x_6624_, 3, v_tree_6627_);
                    lean_ctor_set(v___x_6624_, 2, v_v_6629_);
                    lean_ctor_set(v___x_6624_, 1, v_k_6628_);
                    lean_ctor_set(v___x_6624_, 0, v___x_6669_);
                    v___x_6671_ = v___x_6624_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6675_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6675_, 0, v___x_6669_);
                    lean_ctor_set(v_reuseFailAlloc_6675_, 1, v_k_6628_);
                    lean_ctor_set(v_reuseFailAlloc_6675_, 2, v_v_6629_);
                    lean_ctor_set(v_reuseFailAlloc_6675_, 3, v_tree_6627_);
                    lean_ctor_set(v_reuseFailAlloc_6675_, 4, v_l_6645_);
                    v___x_6671_ = v_reuseFailAlloc_6675_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_6672_ = lean_nat_add(v___x_6621_, v_size_6647_);
                if lean_obj_tag(v_r_6646_) == 0 {
                    v_size_6673_ = lean_ctor_get(v_r_6646_, 0);
                    lean_inc(v_size_6673_);
                    v___y_6657_ = v___x_6671_;
                    v___y_6658_ = v___x_6672_;
                    v___y_6659_ = v_size_6673_;
                    state = 31;
                    continue;
                } else {
                    v___x_6674_ = lean_unsigned_to_nat(0);
                    v___y_6657_ = v___x_6671_;
                    v___y_6658_ = v___x_6672_;
                    v___y_6659_ = v___x_6674_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_6625_ == 0 {
                    lean_ctor_set(v___x_6624_, 4, v_r_6620_);
                    lean_ctor_set(v___x_6624_, 3, v___x_6688_);
                    lean_ctor_set(v___x_6624_, 2, v_v_6618_);
                    lean_ctor_set(v___x_6624_, 1, v_k_6617_);
                    lean_ctor_set(v___x_6624_, 0, v___x_6685_);
                    v___x_6690_ = v___x_6624_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6691_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6691_, 0, v___x_6685_);
                    lean_ctor_set(v_reuseFailAlloc_6691_, 1, v_k_6617_);
                    lean_ctor_set(v_reuseFailAlloc_6691_, 2, v_v_6618_);
                    lean_ctor_set(v_reuseFailAlloc_6691_, 3, v___x_6688_);
                    lean_ctor_set(v_reuseFailAlloc_6691_, 4, v_r_6620_);
                    v___x_6690_ = v_reuseFailAlloc_6691_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6690_;
            }
            38 => {
                if lean_obj_tag(v_l_6619_) == 0 {
                    if lean_obj_tag(v_r_6620_) == 0 {
                        v_k_6702_ = lean_ctor_get(v___x_6626_, 0);
                        lean_inc(v_k_6702_);
                        v_v_6703_ = lean_ctor_get(v___x_6626_, 1);
                        lean_inc(v_v_6703_);
                        lean_dec_ref(v___x_6626_);
                        v_size_6704_ = lean_ctor_get(v_l_6619_, 0);
                        v___x_6705_ = lean_nat_add(v___x_6621_, v_size_6616_);
                        lean_dec(v_size_6616_);
                        v___x_6706_ = lean_nat_add(v___x_6621_, v_size_6704_);
                        if v_isShared_6701_ == 0 {
                            lean_ctor_set(v___x_6700_, 4, v_l_6619_);
                            lean_ctor_set(v___x_6700_, 3, v_tree_6627_);
                            lean_ctor_set(v___x_6700_, 2, v_v_6703_);
                            lean_ctor_set(v___x_6700_, 1, v_k_6702_);
                            lean_ctor_set(v___x_6700_, 0, v___x_6706_);
                            v___x_6708_ = v___x_6700_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_6712_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6712_, 0, v___x_6706_);
                            lean_ctor_set(v_reuseFailAlloc_6712_, 1, v_k_6702_);
                            lean_ctor_set(v_reuseFailAlloc_6712_, 2, v_v_6703_);
                            lean_ctor_set(v_reuseFailAlloc_6712_, 3, v_tree_6627_);
                            lean_ctor_set(v_reuseFailAlloc_6712_, 4, v_l_6619_);
                            v___x_6708_ = v_reuseFailAlloc_6712_;
                            state = 39;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_6616_);
                        v_k_6713_ = lean_ctor_get(v___x_6626_, 0);
                        lean_inc(v_k_6713_);
                        v_v_6714_ = lean_ctor_get(v___x_6626_, 1);
                        lean_inc(v_v_6714_);
                        lean_dec_ref(v___x_6626_);
                        v_k_6715_ = lean_ctor_get(v_l_6619_, 1);
                        v_v_6716_ = lean_ctor_get(v_l_6619_, 2);
                        v_isSharedCheck_6730_ = (!lean_is_exclusive(v_l_6619_)) as u8;
                        if v_isSharedCheck_6730_ == 0 {
                            v_unused_6731_ = lean_ctor_get(v_l_6619_, 4);
                            lean_dec(v_unused_6731_);
                            v_unused_6732_ = lean_ctor_get(v_l_6619_, 3);
                            lean_dec(v_unused_6732_);
                            v_unused_6733_ = lean_ctor_get(v_l_6619_, 0);
                            lean_dec(v_unused_6733_);
                            v___x_6718_ = v_l_6619_;
                            v_isShared_6719_ = v_isSharedCheck_6730_;
                            state = 41;
                            continue;
                        } else {
                            lean_inc(v_v_6716_);
                            lean_inc(v_k_6715_);
                            lean_dec(v_l_6619_);
                            v___x_6718_ = lean_box(0);
                            v_isShared_6719_ = v_isSharedCheck_6730_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_r_6620_) == 0 {
                        lean_dec(v_size_6616_);
                        v_k_6734_ = lean_ctor_get(v___x_6626_, 0);
                        lean_inc(v_k_6734_);
                        v_v_6735_ = lean_ctor_get(v___x_6626_, 1);
                        lean_inc(v_v_6735_);
                        lean_dec_ref(v___x_6626_);
                        v___x_6736_ = lean_unsigned_to_nat(3);
                        if v_isShared_6701_ == 0 {
                            lean_ctor_set(v___x_6700_, 4, v_l_6619_);
                            lean_ctor_set(v___x_6700_, 2, v_v_6735_);
                            lean_ctor_set(v___x_6700_, 1, v_k_6734_);
                            lean_ctor_set(v___x_6700_, 0, v___x_6621_);
                            v___x_6738_ = v___x_6700_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_6742_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6742_, 0, v___x_6621_);
                            lean_ctor_set(v_reuseFailAlloc_6742_, 1, v_k_6734_);
                            lean_ctor_set(v_reuseFailAlloc_6742_, 2, v_v_6735_);
                            lean_ctor_set(v_reuseFailAlloc_6742_, 3, v_l_6619_);
                            lean_ctor_set(v_reuseFailAlloc_6742_, 4, v_l_6619_);
                            v___x_6738_ = v_reuseFailAlloc_6742_;
                            state = 45;
                            continue;
                        }
                    } else {
                        v_k_6743_ = lean_ctor_get(v___x_6626_, 0);
                        lean_inc(v_k_6743_);
                        v_v_6744_ = lean_ctor_get(v___x_6626_, 1);
                        lean_inc(v_v_6744_);
                        lean_dec_ref(v___x_6626_);
                        if v_isShared_6701_ == 0 {
                            lean_ctor_set(v___x_6700_, 3, v_r_6620_);
                            v___x_6746_ = v___x_6700_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_6751_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_size_6616_);
                            lean_ctor_set(v_reuseFailAlloc_6751_, 1, v_k_6617_);
                            lean_ctor_set(v_reuseFailAlloc_6751_, 2, v_v_6618_);
                            lean_ctor_set(v_reuseFailAlloc_6751_, 3, v_r_6620_);
                            lean_ctor_set(v_reuseFailAlloc_6751_, 4, v_r_6620_);
                            v___x_6746_ = v_reuseFailAlloc_6751_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            39 => {
                if v_isShared_6625_ == 0 {
                    lean_ctor_set(v___x_6624_, 4, v_r_6620_);
                    lean_ctor_set(v___x_6624_, 3, v___x_6708_);
                    lean_ctor_set(v___x_6624_, 2, v_v_6618_);
                    lean_ctor_set(v___x_6624_, 1, v_k_6617_);
                    lean_ctor_set(v___x_6624_, 0, v___x_6705_);
                    v___x_6710_ = v___x_6624_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6711_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6711_, 0, v___x_6705_);
                    lean_ctor_set(v_reuseFailAlloc_6711_, 1, v_k_6617_);
                    lean_ctor_set(v_reuseFailAlloc_6711_, 2, v_v_6618_);
                    lean_ctor_set(v_reuseFailAlloc_6711_, 3, v___x_6708_);
                    lean_ctor_set(v_reuseFailAlloc_6711_, 4, v_r_6620_);
                    v___x_6710_ = v_reuseFailAlloc_6711_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_6710_;
            }
            41 => {
                v___x_6720_ = lean_unsigned_to_nat(3);
                if v_isShared_6719_ == 0 {
                    lean_ctor_set(v___x_6718_, 4, v_r_6620_);
                    lean_ctor_set(v___x_6718_, 3, v_r_6620_);
                    lean_ctor_set(v___x_6718_, 2, v_v_6714_);
                    lean_ctor_set(v___x_6718_, 1, v_k_6713_);
                    lean_ctor_set(v___x_6718_, 0, v___x_6621_);
                    v___x_6722_ = v___x_6718_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_6729_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6729_, 0, v___x_6621_);
                    lean_ctor_set(v_reuseFailAlloc_6729_, 1, v_k_6713_);
                    lean_ctor_set(v_reuseFailAlloc_6729_, 2, v_v_6714_);
                    lean_ctor_set(v_reuseFailAlloc_6729_, 3, v_r_6620_);
                    lean_ctor_set(v_reuseFailAlloc_6729_, 4, v_r_6620_);
                    v___x_6722_ = v_reuseFailAlloc_6729_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_6701_ == 0 {
                    lean_ctor_set(v___x_6700_, 3, v_r_6620_);
                    lean_ctor_set(v___x_6700_, 0, v___x_6621_);
                    v___x_6724_ = v___x_6700_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_6728_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6728_, 0, v___x_6621_);
                    lean_ctor_set(v_reuseFailAlloc_6728_, 1, v_k_6617_);
                    lean_ctor_set(v_reuseFailAlloc_6728_, 2, v_v_6618_);
                    lean_ctor_set(v_reuseFailAlloc_6728_, 3, v_r_6620_);
                    lean_ctor_set(v_reuseFailAlloc_6728_, 4, v_r_6620_);
                    v___x_6724_ = v_reuseFailAlloc_6728_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_6625_ == 0 {
                    lean_ctor_set(v___x_6624_, 4, v___x_6724_);
                    lean_ctor_set(v___x_6624_, 3, v___x_6722_);
                    lean_ctor_set(v___x_6624_, 2, v_v_6716_);
                    lean_ctor_set(v___x_6624_, 1, v_k_6715_);
                    lean_ctor_set(v___x_6624_, 0, v___x_6720_);
                    v___x_6726_ = v___x_6624_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6727_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6727_, 0, v___x_6720_);
                    lean_ctor_set(v_reuseFailAlloc_6727_, 1, v_k_6715_);
                    lean_ctor_set(v_reuseFailAlloc_6727_, 2, v_v_6716_);
                    lean_ctor_set(v_reuseFailAlloc_6727_, 3, v___x_6722_);
                    lean_ctor_set(v_reuseFailAlloc_6727_, 4, v___x_6724_);
                    v___x_6726_ = v_reuseFailAlloc_6727_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_6726_;
            }
            45 => {
                if v_isShared_6625_ == 0 {
                    lean_ctor_set(v___x_6624_, 4, v_r_6620_);
                    lean_ctor_set(v___x_6624_, 3, v___x_6738_);
                    lean_ctor_set(v___x_6624_, 2, v_v_6618_);
                    lean_ctor_set(v___x_6624_, 1, v_k_6617_);
                    lean_ctor_set(v___x_6624_, 0, v___x_6736_);
                    v___x_6740_ = v___x_6624_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6741_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6741_, 0, v___x_6736_);
                    lean_ctor_set(v_reuseFailAlloc_6741_, 1, v_k_6617_);
                    lean_ctor_set(v_reuseFailAlloc_6741_, 2, v_v_6618_);
                    lean_ctor_set(v_reuseFailAlloc_6741_, 3, v___x_6738_);
                    lean_ctor_set(v_reuseFailAlloc_6741_, 4, v_r_6620_);
                    v___x_6740_ = v_reuseFailAlloc_6741_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_6740_;
            }
            47 => {
                v___x_6747_ = lean_unsigned_to_nat(2);
                if v_isShared_6625_ == 0 {
                    lean_ctor_set(v___x_6624_, 4, v___x_6746_);
                    lean_ctor_set(v___x_6624_, 3, v_r_6620_);
                    lean_ctor_set(v___x_6624_, 2, v_v_6744_);
                    lean_ctor_set(v___x_6624_, 1, v_k_6743_);
                    lean_ctor_set(v___x_6624_, 0, v___x_6747_);
                    v___x_6749_ = v___x_6624_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_6750_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6750_, 0, v___x_6747_);
                    lean_ctor_set(v_reuseFailAlloc_6750_, 1, v_k_6743_);
                    lean_ctor_set(v_reuseFailAlloc_6750_, 2, v_v_6744_);
                    lean_ctor_set(v_reuseFailAlloc_6750_, 3, v_r_6620_);
                    lean_ctor_set(v_reuseFailAlloc_6750_, 4, v___x_6746_);
                    v___x_6749_ = v_reuseFailAlloc_6750_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_6749_;
            }
            49 => {
                v___x_6767_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_6617_, v_v_6618_, v_l_6619_, v_r_6620_,
                );
                v_tree_6768_ = lean_ctor_get(v___x_6767_, 2);
                lean_inc(v_tree_6768_);
                if lean_obj_tag(v_tree_6768_) == 0 {
                    v_k_6769_ = lean_ctor_get(v___x_6767_, 0);
                    lean_inc(v_k_6769_);
                    v_v_6770_ = lean_ctor_get(v___x_6767_, 1);
                    lean_inc(v_v_6770_);
                    lean_dec_ref(v___x_6767_);
                    v_size_6771_ = lean_ctor_get(v_tree_6768_, 0);
                    v___x_6772_ = lean_unsigned_to_nat(3);
                    v___x_6773_ = lean_nat_mul(v___x_6772_, v_size_6771_);
                    v___x_6774_ = lean_nat_dec_lt(v___x_6773_, v_size_6611_);
                    lean_dec(v___x_6773_);
                    if v___x_6774_ == 0 {
                        lean_dec(v_r_6615_);
                        v___x_6775_ = lean_nat_add(v___x_6621_, v_size_6611_);
                        v___x_6776_ = lean_nat_add(v___x_6775_, v_size_6771_);
                        lean_dec(v___x_6775_);
                        if v_isShared_6766_ == 0 {
                            lean_ctor_set(v___x_6765_, 4, v_tree_6768_);
                            lean_ctor_set(v___x_6765_, 3, v_l_6440_);
                            lean_ctor_set(v___x_6765_, 2, v_v_6770_);
                            lean_ctor_set(v___x_6765_, 1, v_k_6769_);
                            lean_ctor_set(v___x_6765_, 0, v___x_6776_);
                            v___x_6778_ = v___x_6765_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_6779_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6779_, 0, v___x_6776_);
                            lean_ctor_set(v_reuseFailAlloc_6779_, 1, v_k_6769_);
                            lean_ctor_set(v_reuseFailAlloc_6779_, 2, v_v_6770_);
                            lean_ctor_set(v_reuseFailAlloc_6779_, 3, v_l_6440_);
                            lean_ctor_set(v_reuseFailAlloc_6779_, 4, v_tree_6768_);
                            v___x_6778_ = v_reuseFailAlloc_6779_;
                            state = 50;
                            continue;
                        }
                    } else {
                        lean_inc(v_l_6614_);
                        lean_inc(v_v_6613_);
                        lean_inc(v_k_6612_);
                        lean_inc(v_size_6611_);
                        v_isSharedCheck_6845_ = (!lean_is_exclusive(v_l_6440_)) as u8;
                        if v_isSharedCheck_6845_ == 0 {
                            v_unused_6846_ = lean_ctor_get(v_l_6440_, 4);
                            lean_dec(v_unused_6846_);
                            v_unused_6847_ = lean_ctor_get(v_l_6440_, 3);
                            lean_dec(v_unused_6847_);
                            v_unused_6848_ = lean_ctor_get(v_l_6440_, 2);
                            lean_dec(v_unused_6848_);
                            v_unused_6849_ = lean_ctor_get(v_l_6440_, 1);
                            lean_dec(v_unused_6849_);
                            v_unused_6850_ = lean_ctor_get(v_l_6440_, 0);
                            lean_dec(v_unused_6850_);
                            v___x_6781_ = v_l_6440_;
                            v_isShared_6782_ = v_isSharedCheck_6845_;
                            state = 51;
                            continue;
                        } else {
                            lean_dec(v_l_6440_);
                            v___x_6781_ = lean_box(0);
                            v_isShared_6782_ = v_isSharedCheck_6845_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if lean_obj_tag(v_l_6614_) == 0 {
                        lean_inc_ref(v_l_6614_);
                        lean_inc(v_v_6613_);
                        lean_inc(v_k_6612_);
                        lean_inc(v_size_6611_);
                        v_isSharedCheck_6874_ = (!lean_is_exclusive(v_l_6440_)) as u8;
                        if v_isSharedCheck_6874_ == 0 {
                            v_unused_6875_ = lean_ctor_get(v_l_6440_, 4);
                            lean_dec(v_unused_6875_);
                            v_unused_6876_ = lean_ctor_get(v_l_6440_, 3);
                            lean_dec(v_unused_6876_);
                            v_unused_6877_ = lean_ctor_get(v_l_6440_, 2);
                            lean_dec(v_unused_6877_);
                            v_unused_6878_ = lean_ctor_get(v_l_6440_, 1);
                            lean_dec(v_unused_6878_);
                            v_unused_6879_ = lean_ctor_get(v_l_6440_, 0);
                            lean_dec(v_unused_6879_);
                            v___x_6852_ = v_l_6440_;
                            v_isShared_6853_ = v_isSharedCheck_6874_;
                            state = 61;
                            continue;
                        } else {
                            lean_dec(v_l_6440_);
                            v___x_6852_ = lean_box(0);
                            v_isShared_6853_ = v_isSharedCheck_6874_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_r_6615_) == 0 {
                            lean_inc(v_l_6614_);
                            lean_inc(v_v_6613_);
                            lean_inc(v_k_6612_);
                            v_isSharedCheck_6904_ = (!lean_is_exclusive(v_l_6440_)) as u8;
                            if v_isSharedCheck_6904_ == 0 {
                                v_unused_6905_ = lean_ctor_get(v_l_6440_, 4);
                                lean_dec(v_unused_6905_);
                                v_unused_6906_ = lean_ctor_get(v_l_6440_, 3);
                                lean_dec(v_unused_6906_);
                                v_unused_6907_ = lean_ctor_get(v_l_6440_, 2);
                                lean_dec(v_unused_6907_);
                                v_unused_6908_ = lean_ctor_get(v_l_6440_, 1);
                                lean_dec(v_unused_6908_);
                                v_unused_6909_ = lean_ctor_get(v_l_6440_, 0);
                                lean_dec(v_unused_6909_);
                                v___x_6881_ = v_l_6440_;
                                v_isShared_6882_ = v_isSharedCheck_6904_;
                                state = 66;
                                continue;
                            } else {
                                lean_dec(v_l_6440_);
                                v___x_6881_ = lean_box(0);
                                v_isShared_6882_ = v_isSharedCheck_6904_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_6910_ = lean_ctor_get(v___x_6767_, 0);
                            lean_inc(v_k_6910_);
                            v_v_6911_ = lean_ctor_get(v___x_6767_, 1);
                            lean_inc(v_v_6911_);
                            lean_dec_ref(v___x_6767_);
                            v___x_6912_ = lean_unsigned_to_nat(2);
                            if v_isShared_6766_ == 0 {
                                lean_ctor_set(v___x_6765_, 4, v_r_6615_);
                                lean_ctor_set(v___x_6765_, 3, v_l_6440_);
                                lean_ctor_set(v___x_6765_, 2, v_v_6911_);
                                lean_ctor_set(v___x_6765_, 1, v_k_6910_);
                                lean_ctor_set(v___x_6765_, 0, v___x_6912_);
                                v___x_6914_ = v___x_6765_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_6915_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6912_);
                                lean_ctor_set(v_reuseFailAlloc_6915_, 1, v_k_6910_);
                                lean_ctor_set(v_reuseFailAlloc_6915_, 2, v_v_6911_);
                                lean_ctor_set(v_reuseFailAlloc_6915_, 3, v_l_6440_);
                                lean_ctor_set(v_reuseFailAlloc_6915_, 4, v_r_6615_);
                                v___x_6914_ = v_reuseFailAlloc_6915_;
                                state = 71;
                                continue;
                            }
                        }
                    }
                }
            }
            50 => {
                return v___x_6778_;
            }
            51 => {
                v_size_6783_ = lean_ctor_get(v_l_6614_, 0);
                v_size_6784_ = lean_ctor_get(v_r_6615_, 0);
                v_k_6785_ = lean_ctor_get(v_r_6615_, 1);
                v_v_6786_ = lean_ctor_get(v_r_6615_, 2);
                v_l_6787_ = lean_ctor_get(v_r_6615_, 3);
                v_r_6788_ = lean_ctor_get(v_r_6615_, 4);
                v___x_6789_ = lean_unsigned_to_nat(2);
                v___x_6790_ = lean_nat_mul(v___x_6789_, v_size_6783_);
                v___x_6791_ = lean_nat_dec_lt(v_size_6784_, v___x_6790_);
                lean_dec(v___x_6790_);
                if v___x_6791_ == 0 {
                    lean_inc(v_r_6788_);
                    lean_inc(v_l_6787_);
                    lean_inc(v_v_6786_);
                    lean_inc(v_k_6785_);
                    lean_del_object(v___x_6781_);
                    v_isSharedCheck_6829_ = (!lean_is_exclusive(v_r_6615_)) as u8;
                    if v_isSharedCheck_6829_ == 0 {
                        v_unused_6830_ = lean_ctor_get(v_r_6615_, 4);
                        lean_dec(v_unused_6830_);
                        v_unused_6831_ = lean_ctor_get(v_r_6615_, 3);
                        lean_dec(v_unused_6831_);
                        v_unused_6832_ = lean_ctor_get(v_r_6615_, 2);
                        lean_dec(v_unused_6832_);
                        v_unused_6833_ = lean_ctor_get(v_r_6615_, 1);
                        lean_dec(v_unused_6833_);
                        v_unused_6834_ = lean_ctor_get(v_r_6615_, 0);
                        lean_dec(v_unused_6834_);
                        v___x_6793_ = v_r_6615_;
                        v_isShared_6794_ = v_isSharedCheck_6829_;
                        state = 52;
                        continue;
                    } else {
                        lean_dec(v_r_6615_);
                        v___x_6793_ = lean_box(0);
                        v_isShared_6794_ = v_isSharedCheck_6829_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_6835_ = lean_nat_add(v___x_6621_, v_size_6611_);
                    lean_dec(v_size_6611_);
                    v___x_6836_ = lean_nat_add(v___x_6835_, v_size_6771_);
                    lean_dec(v___x_6835_);
                    v___x_6837_ = lean_nat_add(v___x_6621_, v_size_6771_);
                    v___x_6838_ = lean_nat_add(v___x_6837_, v_size_6784_);
                    lean_dec(v___x_6837_);
                    if v_isShared_6766_ == 0 {
                        lean_ctor_set(v___x_6765_, 4, v_tree_6768_);
                        lean_ctor_set(v___x_6765_, 3, v_r_6615_);
                        lean_ctor_set(v___x_6765_, 2, v_v_6770_);
                        lean_ctor_set(v___x_6765_, 1, v_k_6769_);
                        lean_ctor_set(v___x_6765_, 0, v___x_6838_);
                        v___x_6840_ = v___x_6765_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_6844_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6844_, 0, v___x_6838_);
                        lean_ctor_set(v_reuseFailAlloc_6844_, 1, v_k_6769_);
                        lean_ctor_set(v_reuseFailAlloc_6844_, 2, v_v_6770_);
                        lean_ctor_set(v_reuseFailAlloc_6844_, 3, v_r_6615_);
                        lean_ctor_set(v_reuseFailAlloc_6844_, 4, v_tree_6768_);
                        v___x_6840_ = v_reuseFailAlloc_6844_;
                        state = 59;
                        continue;
                    }
                }
            }
            52 => {
                v___x_6795_ = lean_nat_add(v___x_6621_, v_size_6611_);
                lean_dec(v_size_6611_);
                v___x_6796_ = lean_nat_add(v___x_6795_, v_size_6771_);
                lean_dec(v___x_6795_);
                v___x_6817_ = lean_nat_add(v___x_6621_, v_size_6783_);
                if lean_obj_tag(v_l_6787_) == 0 {
                    v_size_6827_ = lean_ctor_get(v_l_6787_, 0);
                    lean_inc(v_size_6827_);
                    v___y_6819_ = v_size_6827_;
                    state = 57;
                    continue;
                } else {
                    v___x_6828_ = lean_unsigned_to_nat(0);
                    v___y_6819_ = v___x_6828_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_6801_ = lean_nat_add(v___y_6798_, v___y_6800_);
                lean_dec(v___y_6800_);
                lean_dec(v___y_6798_);
                lean_inc_ref(v_tree_6768_);
                if v_isShared_6794_ == 0 {
                    lean_ctor_set(v___x_6793_, 4, v_tree_6768_);
                    lean_ctor_set(v___x_6793_, 3, v_r_6788_);
                    lean_ctor_set(v___x_6793_, 2, v_v_6770_);
                    lean_ctor_set(v___x_6793_, 1, v_k_6769_);
                    lean_ctor_set(v___x_6793_, 0, v___x_6801_);
                    v___x_6803_ = v___x_6793_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_6816_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6816_, 0, v___x_6801_);
                    lean_ctor_set(v_reuseFailAlloc_6816_, 1, v_k_6769_);
                    lean_ctor_set(v_reuseFailAlloc_6816_, 2, v_v_6770_);
                    lean_ctor_set(v_reuseFailAlloc_6816_, 3, v_r_6788_);
                    lean_ctor_set(v_reuseFailAlloc_6816_, 4, v_tree_6768_);
                    v___x_6803_ = v_reuseFailAlloc_6816_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_6810_ = (!lean_is_exclusive(v_tree_6768_)) as u8;
                if v_isSharedCheck_6810_ == 0 {
                    v_unused_6811_ = lean_ctor_get(v_tree_6768_, 4);
                    lean_dec(v_unused_6811_);
                    v_unused_6812_ = lean_ctor_get(v_tree_6768_, 3);
                    lean_dec(v_unused_6812_);
                    v_unused_6813_ = lean_ctor_get(v_tree_6768_, 2);
                    lean_dec(v_unused_6813_);
                    v_unused_6814_ = lean_ctor_get(v_tree_6768_, 1);
                    lean_dec(v_unused_6814_);
                    v_unused_6815_ = lean_ctor_get(v_tree_6768_, 0);
                    lean_dec(v_unused_6815_);
                    v___x_6805_ = v_tree_6768_;
                    v_isShared_6806_ = v_isSharedCheck_6810_;
                    state = 55;
                    continue;
                } else {
                    lean_dec(v_tree_6768_);
                    v___x_6805_ = lean_box(0);
                    v_isShared_6806_ = v_isSharedCheck_6810_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_6806_ == 0 {
                    lean_ctor_set(v___x_6805_, 4, v___x_6803_);
                    lean_ctor_set(v___x_6805_, 3, v___y_6799_);
                    lean_ctor_set(v___x_6805_, 2, v_v_6786_);
                    lean_ctor_set(v___x_6805_, 1, v_k_6785_);
                    lean_ctor_set(v___x_6805_, 0, v___x_6796_);
                    v___x_6808_ = v___x_6805_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_6809_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 0, v___x_6796_);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 1, v_k_6785_);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 2, v_v_6786_);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 3, v___y_6799_);
                    lean_ctor_set(v_reuseFailAlloc_6809_, 4, v___x_6803_);
                    v___x_6808_ = v_reuseFailAlloc_6809_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_6808_;
            }
            57 => {
                v___x_6820_ = lean_nat_add(v___x_6817_, v___y_6819_);
                lean_dec(v___y_6819_);
                lean_dec(v___x_6817_);
                if v_isShared_6766_ == 0 {
                    lean_ctor_set(v___x_6765_, 4, v_l_6787_);
                    lean_ctor_set(v___x_6765_, 3, v_l_6614_);
                    lean_ctor_set(v___x_6765_, 2, v_v_6613_);
                    lean_ctor_set(v___x_6765_, 1, v_k_6612_);
                    lean_ctor_set(v___x_6765_, 0, v___x_6820_);
                    v___x_6822_ = v___x_6765_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_6826_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 0, v___x_6820_);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 1, v_k_6612_);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 2, v_v_6613_);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 3, v_l_6614_);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 4, v_l_6787_);
                    v___x_6822_ = v_reuseFailAlloc_6826_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_6823_ = lean_nat_add(v___x_6621_, v_size_6771_);
                if lean_obj_tag(v_r_6788_) == 0 {
                    v_size_6824_ = lean_ctor_get(v_r_6788_, 0);
                    lean_inc(v_size_6824_);
                    v___y_6798_ = v___x_6823_;
                    v___y_6799_ = v___x_6822_;
                    v___y_6800_ = v_size_6824_;
                    state = 53;
                    continue;
                } else {
                    v___x_6825_ = lean_unsigned_to_nat(0);
                    v___y_6798_ = v___x_6823_;
                    v___y_6799_ = v___x_6822_;
                    v___y_6800_ = v___x_6825_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_6782_ == 0 {
                    lean_ctor_set(v___x_6781_, 4, v___x_6840_);
                    lean_ctor_set(v___x_6781_, 0, v___x_6836_);
                    v___x_6842_ = v___x_6781_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_6843_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 0, v___x_6836_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 1, v_k_6612_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 2, v_v_6613_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 3, v_l_6614_);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 4, v___x_6840_);
                    v___x_6842_ = v_reuseFailAlloc_6843_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_6842_;
            }
            61 => {
                if lean_obj_tag(v_r_6615_) == 0 {
                    v_k_6854_ = lean_ctor_get(v___x_6767_, 0);
                    lean_inc(v_k_6854_);
                    v_v_6855_ = lean_ctor_get(v___x_6767_, 1);
                    lean_inc(v_v_6855_);
                    lean_dec_ref(v___x_6767_);
                    v_size_6856_ = lean_ctor_get(v_r_6615_, 0);
                    v___x_6857_ = lean_nat_add(v___x_6621_, v_size_6611_);
                    lean_dec(v_size_6611_);
                    v___x_6858_ = lean_nat_add(v___x_6621_, v_size_6856_);
                    if v_isShared_6766_ == 0 {
                        lean_ctor_set(v___x_6765_, 4, v_tree_6768_);
                        lean_ctor_set(v___x_6765_, 3, v_r_6615_);
                        lean_ctor_set(v___x_6765_, 2, v_v_6855_);
                        lean_ctor_set(v___x_6765_, 1, v_k_6854_);
                        lean_ctor_set(v___x_6765_, 0, v___x_6858_);
                        v___x_6860_ = v___x_6765_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_6864_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6864_, 0, v___x_6858_);
                        lean_ctor_set(v_reuseFailAlloc_6864_, 1, v_k_6854_);
                        lean_ctor_set(v_reuseFailAlloc_6864_, 2, v_v_6855_);
                        lean_ctor_set(v_reuseFailAlloc_6864_, 3, v_r_6615_);
                        lean_ctor_set(v_reuseFailAlloc_6864_, 4, v_tree_6768_);
                        v___x_6860_ = v_reuseFailAlloc_6864_;
                        state = 62;
                        continue;
                    }
                } else {
                    lean_dec(v_size_6611_);
                    v_k_6865_ = lean_ctor_get(v___x_6767_, 0);
                    lean_inc(v_k_6865_);
                    v_v_6866_ = lean_ctor_get(v___x_6767_, 1);
                    lean_inc(v_v_6866_);
                    lean_dec_ref(v___x_6767_);
                    v___x_6867_ = lean_unsigned_to_nat(3);
                    if v_isShared_6766_ == 0 {
                        lean_ctor_set(v___x_6765_, 4, v_r_6615_);
                        lean_ctor_set(v___x_6765_, 3, v_r_6615_);
                        lean_ctor_set(v___x_6765_, 2, v_v_6866_);
                        lean_ctor_set(v___x_6765_, 1, v_k_6865_);
                        lean_ctor_set(v___x_6765_, 0, v___x_6621_);
                        v___x_6869_ = v___x_6765_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_6873_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6873_, 0, v___x_6621_);
                        lean_ctor_set(v_reuseFailAlloc_6873_, 1, v_k_6865_);
                        lean_ctor_set(v_reuseFailAlloc_6873_, 2, v_v_6866_);
                        lean_ctor_set(v_reuseFailAlloc_6873_, 3, v_r_6615_);
                        lean_ctor_set(v_reuseFailAlloc_6873_, 4, v_r_6615_);
                        v___x_6869_ = v_reuseFailAlloc_6873_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_6853_ == 0 {
                    lean_ctor_set(v___x_6852_, 4, v___x_6860_);
                    lean_ctor_set(v___x_6852_, 0, v___x_6857_);
                    v___x_6862_ = v___x_6852_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_6863_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6863_, 0, v___x_6857_);
                    lean_ctor_set(v_reuseFailAlloc_6863_, 1, v_k_6612_);
                    lean_ctor_set(v_reuseFailAlloc_6863_, 2, v_v_6613_);
                    lean_ctor_set(v_reuseFailAlloc_6863_, 3, v_l_6614_);
                    lean_ctor_set(v_reuseFailAlloc_6863_, 4, v___x_6860_);
                    v___x_6862_ = v_reuseFailAlloc_6863_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_6862_;
            }
            64 => {
                if v_isShared_6853_ == 0 {
                    lean_ctor_set(v___x_6852_, 4, v___x_6869_);
                    lean_ctor_set(v___x_6852_, 0, v___x_6867_);
                    v___x_6871_ = v___x_6852_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_6872_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6872_, 0, v___x_6867_);
                    lean_ctor_set(v_reuseFailAlloc_6872_, 1, v_k_6612_);
                    lean_ctor_set(v_reuseFailAlloc_6872_, 2, v_v_6613_);
                    lean_ctor_set(v_reuseFailAlloc_6872_, 3, v_l_6614_);
                    lean_ctor_set(v_reuseFailAlloc_6872_, 4, v___x_6869_);
                    v___x_6871_ = v_reuseFailAlloc_6872_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_6871_;
            }
            66 => {
                v_k_6883_ = lean_ctor_get(v___x_6767_, 0);
                lean_inc(v_k_6883_);
                v_v_6884_ = lean_ctor_get(v___x_6767_, 1);
                lean_inc(v_v_6884_);
                lean_dec_ref(v___x_6767_);
                v_k_6885_ = lean_ctor_get(v_r_6615_, 1);
                v_v_6886_ = lean_ctor_get(v_r_6615_, 2);
                v_isSharedCheck_6900_ = (!lean_is_exclusive(v_r_6615_)) as u8;
                if v_isSharedCheck_6900_ == 0 {
                    v_unused_6901_ = lean_ctor_get(v_r_6615_, 4);
                    lean_dec(v_unused_6901_);
                    v_unused_6902_ = lean_ctor_get(v_r_6615_, 3);
                    lean_dec(v_unused_6902_);
                    v_unused_6903_ = lean_ctor_get(v_r_6615_, 0);
                    lean_dec(v_unused_6903_);
                    v___x_6888_ = v_r_6615_;
                    v_isShared_6889_ = v_isSharedCheck_6900_;
                    state = 67;
                    continue;
                } else {
                    lean_inc(v_v_6886_);
                    lean_inc(v_k_6885_);
                    lean_dec(v_r_6615_);
                    v___x_6888_ = lean_box(0);
                    v_isShared_6889_ = v_isSharedCheck_6900_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_6890_ = lean_unsigned_to_nat(3);
                if v_isShared_6889_ == 0 {
                    lean_ctor_set(v___x_6888_, 4, v_l_6614_);
                    lean_ctor_set(v___x_6888_, 3, v_l_6614_);
                    lean_ctor_set(v___x_6888_, 2, v_v_6613_);
                    lean_ctor_set(v___x_6888_, 1, v_k_6612_);
                    lean_ctor_set(v___x_6888_, 0, v___x_6621_);
                    v___x_6892_ = v___x_6888_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_6899_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6899_, 0, v___x_6621_);
                    lean_ctor_set(v_reuseFailAlloc_6899_, 1, v_k_6612_);
                    lean_ctor_set(v_reuseFailAlloc_6899_, 2, v_v_6613_);
                    lean_ctor_set(v_reuseFailAlloc_6899_, 3, v_l_6614_);
                    lean_ctor_set(v_reuseFailAlloc_6899_, 4, v_l_6614_);
                    v___x_6892_ = v_reuseFailAlloc_6899_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_6766_ == 0 {
                    lean_ctor_set(v___x_6765_, 4, v_l_6614_);
                    lean_ctor_set(v___x_6765_, 3, v_l_6614_);
                    lean_ctor_set(v___x_6765_, 2, v_v_6884_);
                    lean_ctor_set(v___x_6765_, 1, v_k_6883_);
                    lean_ctor_set(v___x_6765_, 0, v___x_6621_);
                    v___x_6894_ = v___x_6765_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_6898_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6898_, 0, v___x_6621_);
                    lean_ctor_set(v_reuseFailAlloc_6898_, 1, v_k_6883_);
                    lean_ctor_set(v_reuseFailAlloc_6898_, 2, v_v_6884_);
                    lean_ctor_set(v_reuseFailAlloc_6898_, 3, v_l_6614_);
                    lean_ctor_set(v_reuseFailAlloc_6898_, 4, v_l_6614_);
                    v___x_6894_ = v_reuseFailAlloc_6898_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_6882_ == 0 {
                    lean_ctor_set(v___x_6881_, 4, v___x_6894_);
                    lean_ctor_set(v___x_6881_, 3, v___x_6892_);
                    lean_ctor_set(v___x_6881_, 2, v_v_6886_);
                    lean_ctor_set(v___x_6881_, 1, v_k_6885_);
                    lean_ctor_set(v___x_6881_, 0, v___x_6890_);
                    v___x_6896_ = v___x_6881_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_6897_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6897_, 0, v___x_6890_);
                    lean_ctor_set(v_reuseFailAlloc_6897_, 1, v_k_6885_);
                    lean_ctor_set(v_reuseFailAlloc_6897_, 2, v_v_6886_);
                    lean_ctor_set(v_reuseFailAlloc_6897_, 3, v___x_6892_);
                    lean_ctor_set(v_reuseFailAlloc_6897_, 4, v___x_6894_);
                    v___x_6896_ = v_reuseFailAlloc_6897_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_6896_;
            }
            71 => {
                return v___x_6914_;
            }
            72 => {
                return v___x_6936_;
            }
            73 => {
                v_size_6941_ = lean_ctor_get(v_l_6928_, 0);
                v_k_6942_ = lean_ctor_get(v_l_6928_, 1);
                v_v_6943_ = lean_ctor_get(v_l_6928_, 2);
                v_l_6944_ = lean_ctor_get(v_l_6928_, 3);
                v_r_6945_ = lean_ctor_get(v_l_6928_, 4);
                v_size_6946_ = lean_ctor_get(v_r_6929_, 0);
                v___x_6947_ = lean_unsigned_to_nat(2);
                v___x_6948_ = lean_nat_mul(v___x_6947_, v_size_6946_);
                v___x_6949_ = lean_nat_dec_lt(v_size_6941_, v___x_6948_);
                lean_dec(v___x_6948_);
                if v___x_6949_ == 0 {
                    lean_inc(v_r_6945_);
                    lean_inc(v_l_6944_);
                    lean_inc(v_v_6943_);
                    lean_inc(v_k_6942_);
                    v_isSharedCheck_6977_ = (!lean_is_exclusive(v_l_6928_)) as u8;
                    if v_isSharedCheck_6977_ == 0 {
                        v_unused_6978_ = lean_ctor_get(v_l_6928_, 4);
                        lean_dec(v_unused_6978_);
                        v_unused_6979_ = lean_ctor_get(v_l_6928_, 3);
                        lean_dec(v_unused_6979_);
                        v_unused_6980_ = lean_ctor_get(v_l_6928_, 2);
                        lean_dec(v_unused_6980_);
                        v_unused_6981_ = lean_ctor_get(v_l_6928_, 1);
                        lean_dec(v_unused_6981_);
                        v_unused_6982_ = lean_ctor_get(v_l_6928_, 0);
                        lean_dec(v_unused_6982_);
                        v___x_6951_ = v_l_6928_;
                        v_isShared_6952_ = v_isSharedCheck_6977_;
                        state = 74;
                        continue;
                    } else {
                        lean_dec(v_l_6928_);
                        v___x_6951_ = lean_box(0);
                        v_isShared_6952_ = v_isSharedCheck_6977_;
                        state = 74;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6443_);
                    v___x_6983_ = lean_nat_add(v___x_6923_, v_size_6924_);
                    lean_dec(v_size_6924_);
                    v___x_6984_ = lean_nat_add(v___x_6983_, v_size_6925_);
                    lean_dec(v_size_6925_);
                    v___x_6985_ = lean_nat_add(v___x_6983_, v_size_6941_);
                    lean_dec(v___x_6983_);
                    lean_inc_ref(v_impl_6922_);
                    if v_isShared_6940_ == 0 {
                        lean_ctor_set(v___x_6939_, 4, v_l_6928_);
                        lean_ctor_set(v___x_6939_, 3, v_impl_6922_);
                        lean_ctor_set(v___x_6939_, 2, v_v_6439_);
                        lean_ctor_set(v___x_6939_, 1, v_k_6438_);
                        lean_ctor_set(v___x_6939_, 0, v___x_6985_);
                        v___x_6987_ = v___x_6939_;
                        state = 80;
                        continue;
                    } else {
                        v_reuseFailAlloc_7000_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7000_, 0, v___x_6985_);
                        lean_ctor_set(v_reuseFailAlloc_7000_, 1, v_k_6438_);
                        lean_ctor_set(v_reuseFailAlloc_7000_, 2, v_v_6439_);
                        lean_ctor_set(v_reuseFailAlloc_7000_, 3, v_impl_6922_);
                        lean_ctor_set(v_reuseFailAlloc_7000_, 4, v_l_6928_);
                        v___x_6987_ = v_reuseFailAlloc_7000_;
                        state = 80;
                        continue;
                    }
                }
            }
            74 => {
                v___x_6953_ = lean_nat_add(v___x_6923_, v_size_6924_);
                lean_dec(v_size_6924_);
                v___x_6954_ = lean_nat_add(v___x_6953_, v_size_6925_);
                lean_dec(v_size_6925_);
                if lean_obj_tag(v_l_6944_) == 0 {
                    v_size_6975_ = lean_ctor_get(v_l_6944_, 0);
                    lean_inc(v_size_6975_);
                    v___y_6967_ = v_size_6975_;
                    state = 78;
                    continue;
                } else {
                    v___x_6976_ = lean_unsigned_to_nat(0);
                    v___y_6967_ = v___x_6976_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_6959_ = lean_nat_add(v___y_6956_, v___y_6958_);
                lean_dec(v___y_6958_);
                lean_dec(v___y_6956_);
                if v_isShared_6952_ == 0 {
                    lean_ctor_set(v___x_6951_, 4, v_r_6929_);
                    lean_ctor_set(v___x_6951_, 3, v_r_6945_);
                    lean_ctor_set(v___x_6951_, 2, v_v_6927_);
                    lean_ctor_set(v___x_6951_, 1, v_k_6926_);
                    lean_ctor_set(v___x_6951_, 0, v___x_6959_);
                    v___x_6961_ = v___x_6951_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_6965_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6965_, 0, v___x_6959_);
                    lean_ctor_set(v_reuseFailAlloc_6965_, 1, v_k_6926_);
                    lean_ctor_set(v_reuseFailAlloc_6965_, 2, v_v_6927_);
                    lean_ctor_set(v_reuseFailAlloc_6965_, 3, v_r_6945_);
                    lean_ctor_set(v_reuseFailAlloc_6965_, 4, v_r_6929_);
                    v___x_6961_ = v_reuseFailAlloc_6965_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_6940_ == 0 {
                    lean_ctor_set(v___x_6939_, 4, v___x_6961_);
                    lean_ctor_set(v___x_6939_, 3, v___y_6957_);
                    lean_ctor_set(v___x_6939_, 2, v_v_6943_);
                    lean_ctor_set(v___x_6939_, 1, v_k_6942_);
                    lean_ctor_set(v___x_6939_, 0, v___x_6954_);
                    v___x_6963_ = v___x_6939_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_6964_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6964_, 0, v___x_6954_);
                    lean_ctor_set(v_reuseFailAlloc_6964_, 1, v_k_6942_);
                    lean_ctor_set(v_reuseFailAlloc_6964_, 2, v_v_6943_);
                    lean_ctor_set(v_reuseFailAlloc_6964_, 3, v___y_6957_);
                    lean_ctor_set(v_reuseFailAlloc_6964_, 4, v___x_6961_);
                    v___x_6963_ = v_reuseFailAlloc_6964_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_6963_;
            }
            78 => {
                v___x_6968_ = lean_nat_add(v___x_6953_, v___y_6967_);
                lean_dec(v___y_6967_);
                lean_dec(v___x_6953_);
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v_l_6944_);
                    lean_ctor_set(v___x_6443_, 3, v_impl_6922_);
                    lean_ctor_set(v___x_6443_, 0, v___x_6968_);
                    v___x_6970_ = v___x_6443_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_6974_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6974_, 0, v___x_6968_);
                    lean_ctor_set(v_reuseFailAlloc_6974_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_6974_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_6974_, 3, v_impl_6922_);
                    lean_ctor_set(v_reuseFailAlloc_6974_, 4, v_l_6944_);
                    v___x_6970_ = v_reuseFailAlloc_6974_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_6971_ = lean_nat_add(v___x_6923_, v_size_6946_);
                if lean_obj_tag(v_r_6945_) == 0 {
                    v_size_6972_ = lean_ctor_get(v_r_6945_, 0);
                    lean_inc(v_size_6972_);
                    v___y_6956_ = v___x_6971_;
                    v___y_6957_ = v___x_6970_;
                    v___y_6958_ = v_size_6972_;
                    state = 75;
                    continue;
                } else {
                    v___x_6973_ = lean_unsigned_to_nat(0);
                    v___y_6956_ = v___x_6971_;
                    v___y_6957_ = v___x_6970_;
                    v___y_6958_ = v___x_6973_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_6994_ = (!lean_is_exclusive(v_impl_6922_)) as u8;
                if v_isSharedCheck_6994_ == 0 {
                    v_unused_6995_ = lean_ctor_get(v_impl_6922_, 4);
                    lean_dec(v_unused_6995_);
                    v_unused_6996_ = lean_ctor_get(v_impl_6922_, 3);
                    lean_dec(v_unused_6996_);
                    v_unused_6997_ = lean_ctor_get(v_impl_6922_, 2);
                    lean_dec(v_unused_6997_);
                    v_unused_6998_ = lean_ctor_get(v_impl_6922_, 1);
                    lean_dec(v_unused_6998_);
                    v_unused_6999_ = lean_ctor_get(v_impl_6922_, 0);
                    lean_dec(v_unused_6999_);
                    v___x_6989_ = v_impl_6922_;
                    v_isShared_6990_ = v_isSharedCheck_6994_;
                    state = 81;
                    continue;
                } else {
                    lean_dec(v_impl_6922_);
                    v___x_6989_ = lean_box(0);
                    v_isShared_6990_ = v_isSharedCheck_6994_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_6990_ == 0 {
                    lean_ctor_set(v___x_6989_, 4, v_r_6929_);
                    lean_ctor_set(v___x_6989_, 3, v___x_6987_);
                    lean_ctor_set(v___x_6989_, 2, v_v_6927_);
                    lean_ctor_set(v___x_6989_, 1, v_k_6926_);
                    lean_ctor_set(v___x_6989_, 0, v___x_6984_);
                    v___x_6992_ = v___x_6989_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_6993_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6993_, 0, v___x_6984_);
                    lean_ctor_set(v_reuseFailAlloc_6993_, 1, v_k_6926_);
                    lean_ctor_set(v_reuseFailAlloc_6993_, 2, v_v_6927_);
                    lean_ctor_set(v_reuseFailAlloc_6993_, 3, v___x_6987_);
                    lean_ctor_set(v_reuseFailAlloc_6993_, 4, v_r_6929_);
                    v___x_6992_ = v_reuseFailAlloc_6993_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_6992_;
            }
            83 => {
                return v___x_7010_;
            }
            84 => {
                v_size_7020_ = lean_ctor_get(v_l_7012_, 0);
                v___x_7021_ = lean_nat_add(v___x_6923_, v_size_7014_);
                lean_dec(v_size_7014_);
                v___x_7022_ = lean_nat_add(v___x_6923_, v_size_7020_);
                if v_isShared_7019_ == 0 {
                    lean_ctor_set(v___x_7018_, 4, v_l_7012_);
                    lean_ctor_set(v___x_7018_, 3, v_impl_6922_);
                    lean_ctor_set(v___x_7018_, 2, v_v_6439_);
                    lean_ctor_set(v___x_7018_, 1, v_k_6438_);
                    lean_ctor_set(v___x_7018_, 0, v___x_7022_);
                    v___x_7024_ = v___x_7018_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_7028_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7028_, 0, v___x_7022_);
                    lean_ctor_set(v_reuseFailAlloc_7028_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_7028_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_7028_, 3, v_impl_6922_);
                    lean_ctor_set(v_reuseFailAlloc_7028_, 4, v_l_7012_);
                    v___x_7024_ = v_reuseFailAlloc_7028_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v_r_7013_);
                    lean_ctor_set(v___x_6443_, 3, v___x_7024_);
                    lean_ctor_set(v___x_6443_, 2, v_v_7016_);
                    lean_ctor_set(v___x_6443_, 1, v_k_7015_);
                    lean_ctor_set(v___x_6443_, 0, v___x_7021_);
                    v___x_7026_ = v___x_6443_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_7027_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7027_, 0, v___x_7021_);
                    lean_ctor_set(v_reuseFailAlloc_7027_, 1, v_k_7015_);
                    lean_ctor_set(v_reuseFailAlloc_7027_, 2, v_v_7016_);
                    lean_ctor_set(v_reuseFailAlloc_7027_, 3, v___x_7024_);
                    lean_ctor_set(v_reuseFailAlloc_7027_, 4, v_r_7013_);
                    v___x_7026_ = v_reuseFailAlloc_7027_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_7026_;
            }
            87 => {
                v_k_7037_ = lean_ctor_get(v_l_7012_, 1);
                v_v_7038_ = lean_ctor_get(v_l_7012_, 2);
                v_isSharedCheck_7052_ = (!lean_is_exclusive(v_l_7012_)) as u8;
                if v_isSharedCheck_7052_ == 0 {
                    v_unused_7053_ = lean_ctor_get(v_l_7012_, 4);
                    lean_dec(v_unused_7053_);
                    v_unused_7054_ = lean_ctor_get(v_l_7012_, 3);
                    lean_dec(v_unused_7054_);
                    v_unused_7055_ = lean_ctor_get(v_l_7012_, 0);
                    lean_dec(v_unused_7055_);
                    v___x_7040_ = v_l_7012_;
                    v_isShared_7041_ = v_isSharedCheck_7052_;
                    state = 88;
                    continue;
                } else {
                    lean_inc(v_v_7038_);
                    lean_inc(v_k_7037_);
                    lean_dec(v_l_7012_);
                    v___x_7040_ = lean_box(0);
                    v_isShared_7041_ = v_isSharedCheck_7052_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                v___x_7042_ = lean_unsigned_to_nat(3);
                if v_isShared_7041_ == 0 {
                    lean_ctor_set(v___x_7040_, 4, v_r_7013_);
                    lean_ctor_set(v___x_7040_, 3, v_r_7013_);
                    lean_ctor_set(v___x_7040_, 2, v_v_6439_);
                    lean_ctor_set(v___x_7040_, 1, v_k_6438_);
                    lean_ctor_set(v___x_7040_, 0, v___x_6923_);
                    v___x_7044_ = v___x_7040_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_7051_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 0, v___x_6923_);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 3, v_r_7013_);
                    lean_ctor_set(v_reuseFailAlloc_7051_, 4, v_r_7013_);
                    v___x_7044_ = v_reuseFailAlloc_7051_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_7036_ == 0 {
                    lean_ctor_set(v___x_7035_, 3, v_r_7013_);
                    lean_ctor_set(v___x_7035_, 0, v___x_6923_);
                    v___x_7046_ = v___x_7035_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_7050_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_6923_);
                    lean_ctor_set(v_reuseFailAlloc_7050_, 1, v_k_7032_);
                    lean_ctor_set(v_reuseFailAlloc_7050_, 2, v_v_7033_);
                    lean_ctor_set(v_reuseFailAlloc_7050_, 3, v_r_7013_);
                    lean_ctor_set(v_reuseFailAlloc_7050_, 4, v_r_7013_);
                    v___x_7046_ = v_reuseFailAlloc_7050_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v___x_7046_);
                    lean_ctor_set(v___x_6443_, 3, v___x_7044_);
                    lean_ctor_set(v___x_6443_, 2, v_v_7038_);
                    lean_ctor_set(v___x_6443_, 1, v_k_7037_);
                    lean_ctor_set(v___x_6443_, 0, v___x_7042_);
                    v___x_7048_ = v___x_6443_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_7049_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7049_, 0, v___x_7042_);
                    lean_ctor_set(v_reuseFailAlloc_7049_, 1, v_k_7037_);
                    lean_ctor_set(v_reuseFailAlloc_7049_, 2, v_v_7038_);
                    lean_ctor_set(v_reuseFailAlloc_7049_, 3, v___x_7044_);
                    lean_ctor_set(v_reuseFailAlloc_7049_, 4, v___x_7046_);
                    v___x_7048_ = v_reuseFailAlloc_7049_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_7048_;
            }
            92 => {
                v___x_7066_ = lean_unsigned_to_nat(3);
                if v_isShared_7065_ == 0 {
                    lean_ctor_set(v___x_7064_, 4, v_l_7012_);
                    lean_ctor_set(v___x_7064_, 2, v_v_6439_);
                    lean_ctor_set(v___x_7064_, 1, v_k_6438_);
                    lean_ctor_set(v___x_7064_, 0, v___x_6923_);
                    v___x_7068_ = v___x_7064_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_7072_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 0, v___x_6923_);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 3, v_l_7012_);
                    lean_ctor_set(v_reuseFailAlloc_7072_, 4, v_l_7012_);
                    v___x_7068_ = v_reuseFailAlloc_7072_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v_r_7060_);
                    lean_ctor_set(v___x_6443_, 3, v___x_7068_);
                    lean_ctor_set(v___x_6443_, 2, v_v_7062_);
                    lean_ctor_set(v___x_6443_, 1, v_k_7061_);
                    lean_ctor_set(v___x_6443_, 0, v___x_7066_);
                    v___x_7070_ = v___x_6443_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_7071_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7071_, 0, v___x_7066_);
                    lean_ctor_set(v_reuseFailAlloc_7071_, 1, v_k_7061_);
                    lean_ctor_set(v_reuseFailAlloc_7071_, 2, v_v_7062_);
                    lean_ctor_set(v_reuseFailAlloc_7071_, 3, v___x_7068_);
                    lean_ctor_set(v_reuseFailAlloc_7071_, 4, v_r_7060_);
                    v___x_7070_ = v_reuseFailAlloc_7071_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                return v___x_7070_;
            }
            95 => {
                if v_isShared_7082_ == 0 {
                    lean_ctor_set(v___x_7081_, 3, v_r_7060_);
                    v___x_7084_ = v___x_7081_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_7089_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7089_, 0, v_size_7077_);
                    lean_ctor_set(v_reuseFailAlloc_7089_, 1, v_k_7078_);
                    lean_ctor_set(v_reuseFailAlloc_7089_, 2, v_v_7079_);
                    lean_ctor_set(v_reuseFailAlloc_7089_, 3, v_r_7060_);
                    lean_ctor_set(v_reuseFailAlloc_7089_, 4, v_r_7060_);
                    v___x_7084_ = v_reuseFailAlloc_7089_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                v___x_7085_ = lean_unsigned_to_nat(2);
                if v_isShared_6444_ == 0 {
                    lean_ctor_set(v___x_6443_, 4, v___x_7084_);
                    lean_ctor_set(v___x_6443_, 3, v_r_7060_);
                    lean_ctor_set(v___x_6443_, 0, v___x_7085_);
                    v___x_7087_ = v___x_6443_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_7088_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7088_, 0, v___x_7085_);
                    lean_ctor_set(v_reuseFailAlloc_7088_, 1, v_k_6438_);
                    lean_ctor_set(v_reuseFailAlloc_7088_, 2, v_v_6439_);
                    lean_ctor_set(v_reuseFailAlloc_7088_, 3, v_r_7060_);
                    lean_ctor_set(v_reuseFailAlloc_7088_, 4, v___x_7084_);
                    v___x_7087_ = v_reuseFailAlloc_7088_;
                    state = 97;
                    continue;
                }
            }
            97 => {
                return v___x_7087_;
            }
            98 => {
                return v___x_7094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(
    mut v_k_7098_: *mut LeanObject,
    mut v_t_7099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7100_: *mut LeanObject = core::ptr::null_mut();
    v_res_7100_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_7098_, v_t_7099_);
    lean_dec(v_k_7098_);
    return v_res_7100_;
}
pub unsafe fn l_Lean_IR_LocalContext_eraseJoinPointDecl(
    mut v_ctx_7101_: *mut LeanObject,
    mut v_j_7102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7103_: *mut LeanObject = core::ptr::null_mut();
    v___x_7103_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_7102_, v_ctx_7101_);
    return v___x_7103_;
}
pub unsafe fn l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(
    mut v_ctx_7104_: *mut LeanObject,
    mut v_j_7105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7106_: *mut LeanObject = core::ptr::null_mut();
    v_res_7106_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_7104_, v_j_7105_);
    lean_dec(v_j_7105_);
    return v_res_7106_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(
    mut v_00_u03b2_7107_: *mut LeanObject,
    mut v_k_7108_: *mut LeanObject,
    mut v_t_7109_: *mut LeanObject,
    mut v_h_7110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    v___x_7111_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_7108_, v_t_7109_);
    return v___x_7111_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(
    mut v_00_u03b2_7112_: *mut LeanObject,
    mut v_k_7113_: *mut LeanObject,
    mut v_t_7114_: *mut LeanObject,
    mut v_h_7115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7116_: *mut LeanObject = core::ptr::null_mut();
    v_res_7116_ =
        l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(
            v_00_u03b2_7112_,
            v_k_7113_,
            v_t_7114_,
            v_h_7115_,
        );
    lean_dec(v_k_7113_);
    return v_res_7116_;
}
pub unsafe fn l_Lean_IR_LocalContext_getType(
    mut v_ctx_7117_: *mut LeanObject,
    mut v_x_7118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7123_: u8 = 0;
    let mut v_a_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7133_: u8 = 0;
    let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7119_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_7117_, v_x_7118_);
                if lean_obj_tag(v___x_7119_) == 1 {
                    v_val_7120_ = lean_ctor_get(v___x_7119_, 0);
                    v_isSharedCheck_7133_ = (!lean_is_exclusive(v___x_7119_)) as u8;
                    if v_isSharedCheck_7133_ == 0 {
                        v___x_7122_ = v___x_7119_;
                        v_isShared_7123_ = v_isSharedCheck_7133_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7120_);
                        lean_dec(v___x_7119_);
                        v___x_7122_ = lean_box(0);
                        v_isShared_7123_ = v_isSharedCheck_7133_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7119_);
                    v___x_7134_ = lean_box(0);
                    return v___x_7134_;
                }
            }
            1 => match lean_obj_tag(v_val_7120_) {
                0 => {
                    v_a_7124_ = lean_ctor_get(v_val_7120_, 0);
                    lean_inc(v_a_7124_);
                    lean_dec_ref_known(v_val_7120_, 1);
                    if v_isShared_7123_ == 0 {
                        lean_ctor_set(v___x_7122_, 0, v_a_7124_);
                        v___x_7126_ = v___x_7122_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7127_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7127_, 0, v_a_7124_);
                        v___x_7126_ = v_reuseFailAlloc_7127_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_a_7128_ = lean_ctor_get(v_val_7120_, 0);
                    lean_inc(v_a_7128_);
                    lean_dec_ref_known(v_val_7120_, 2);
                    if v_isShared_7123_ == 0 {
                        lean_ctor_set(v___x_7122_, 0, v_a_7128_);
                        v___x_7130_ = v___x_7122_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7131_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7131_, 0, v_a_7128_);
                        v___x_7130_ = v_reuseFailAlloc_7131_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_del_object(v___x_7122_);
                    lean_dec(v_val_7120_);
                    v___x_7132_ = lean_box(0);
                    return v___x_7132_;
                }
            },
            2 => {
                return v___x_7126_;
            }
            3 => {
                return v___x_7130_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContext_getType___boxed(
    mut v_ctx_7135_: *mut LeanObject,
    mut v_x_7136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7137_: *mut LeanObject = core::ptr::null_mut();
    v_res_7137_ = l_Lean_IR_LocalContext_getType(v_ctx_7135_, v_x_7136_);
    lean_dec(v_x_7136_);
    lean_dec(v_ctx_7135_);
    return v_res_7137_;
}
pub unsafe fn l_Lean_IR_LocalContext_getValue(
    mut v_ctx_7138_: *mut LeanObject,
    mut v_x_7139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7144_: u8 = 0;
    let mut v_a_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7150_: u8 = 0;
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_7138_, v_x_7139_);
                if lean_obj_tag(v___x_7140_) == 1 {
                    v_val_7141_ = lean_ctor_get(v___x_7140_, 0);
                    v_isSharedCheck_7150_ = (!lean_is_exclusive(v___x_7140_)) as u8;
                    if v_isSharedCheck_7150_ == 0 {
                        v___x_7143_ = v___x_7140_;
                        v_isShared_7144_ = v_isSharedCheck_7150_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_7141_);
                        lean_dec(v___x_7140_);
                        v___x_7143_ = lean_box(0);
                        v_isShared_7144_ = v_isSharedCheck_7150_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7140_);
                    v___x_7151_ = lean_box(0);
                    return v___x_7151_;
                }
            }
            1 => {
                if lean_obj_tag(v_val_7141_) == 1 {
                    v_a_7145_ = lean_ctor_get(v_val_7141_, 1);
                    lean_inc_ref(v_a_7145_);
                    lean_dec_ref_known(v_val_7141_, 2);
                    if v_isShared_7144_ == 0 {
                        lean_ctor_set(v___x_7143_, 0, v_a_7145_);
                        v___x_7147_ = v___x_7143_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7148_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7148_, 0, v_a_7145_);
                        v___x_7147_ = v_reuseFailAlloc_7148_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7143_);
                    lean_dec(v_val_7141_);
                    v___x_7149_ = lean_box(0);
                    return v___x_7149_;
                }
            }
            2 => {
                return v___x_7147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContext_getValue___boxed(
    mut v_ctx_7152_: *mut LeanObject,
    mut v_x_7153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7154_: *mut LeanObject = core::ptr::null_mut();
    v_res_7154_ = l_Lean_IR_LocalContext_getValue(v_ctx_7152_, v_x_7153_);
    lean_dec(v_x_7153_);
    lean_dec(v_ctx_7152_);
    return v_res_7154_;
}
pub unsafe fn l_Lean_IR_VarId_alphaEqv(
    mut v_00_u03c1_7155_: *mut LeanObject,
    mut v_v_u2081_7156_: *mut LeanObject,
    mut v_v_u2082_7157_: *mut LeanObject,
) -> u8 {
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    v___x_7158_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_00_u03c1_7155_, v_v_u2081_7156_);
    if lean_obj_tag(v___x_7158_) == 0 {
        let mut v___x_7159_: u8 = 0;
        v___x_7159_ = lean_nat_dec_eq(v_v_u2081_7156_, v_v_u2082_7157_);
        return v___x_7159_;
    } else {
        let mut v_val_7160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7161_: u8 = 0;
        v_val_7160_ = lean_ctor_get(v___x_7158_, 0);
        lean_inc(v_val_7160_);
        lean_dec_ref_known(v___x_7158_, 1);
        v___x_7161_ = lean_nat_dec_eq(v_val_7160_, v_v_u2082_7157_);
        lean_dec(v_val_7160_);
        return v___x_7161_;
    }
}
pub unsafe fn l_Lean_IR_VarId_alphaEqv___boxed(
    mut v_00_u03c1_7162_: *mut LeanObject,
    mut v_v_u2081_7163_: *mut LeanObject,
    mut v_v_u2082_7164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7165_: u8 = 0;
    let mut v_r_7166_: *mut LeanObject = core::ptr::null_mut();
    v_res_7165_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7162_, v_v_u2081_7163_, v_v_u2082_7164_);
    lean_dec(v_v_u2082_7164_);
    lean_dec(v_v_u2081_7163_);
    lean_dec(v_00_u03c1_7162_);
    v_r_7166_ = lean_box((v_res_7165_) as usize);
    return v_r_7166_;
}
pub unsafe fn l_Lean_IR_Arg_alphaEqv(
    mut v_00_u03c1_7169_: *mut LeanObject,
    mut v_x_7170_: *mut LeanObject,
    mut v_x_7171_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_7170_) == 0 {
        if lean_obj_tag(v_x_7171_) == 0 {
            let mut v_id_7172_: *mut LeanObject = core::ptr::null_mut();
            let mut v_id_7173_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_7174_: u8 = 0;
            v_id_7172_ = lean_ctor_get(v_x_7170_, 0);
            v_id_7173_ = lean_ctor_get(v_x_7171_, 0);
            v___x_7174_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7169_, v_id_7172_, v_id_7173_);
            return v___x_7174_;
        } else {
            let mut v___x_7175_: u8 = 0;
            v___x_7175_ = 0;
            return v___x_7175_;
        }
    } else {
        if lean_obj_tag(v_x_7171_) == 1 {
            let mut v___x_7176_: u8 = 0;
            v___x_7176_ = 1;
            return v___x_7176_;
        } else {
            let mut v___x_7177_: u8 = 0;
            v___x_7177_ = 0;
            return v___x_7177_;
        }
    }
}
pub unsafe fn l_Lean_IR_Arg_alphaEqv___boxed(
    mut v_00_u03c1_7178_: *mut LeanObject,
    mut v_x_7179_: *mut LeanObject,
    mut v_x_7180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7181_: u8 = 0;
    let mut v_r_7182_: *mut LeanObject = core::ptr::null_mut();
    v_res_7181_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_7178_, v_x_7179_, v_x_7180_);
    lean_dec(v_x_7180_);
    lean_dec(v_x_7179_);
    lean_dec(v_00_u03c1_7178_);
    v_r_7182_ = lean_box((v_res_7181_) as usize);
    return v_r_7182_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(
    mut v_00_u03c1_7185_: *mut LeanObject,
    mut v_xs_7186_: *mut LeanObject,
    mut v_ys_7187_: *mut LeanObject,
    mut v_x_7188_: *mut LeanObject,
) -> u8 {
    let mut v_zero_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7190_: u8 = 0;
    let mut v_one_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7189_ = lean_unsigned_to_nat(0);
                v_isZero_7190_ = lean_nat_dec_eq(v_x_7188_, v_zero_7189_);
                if v_isZero_7190_ == 1 {
                    lean_dec(v_x_7188_);
                    return v_isZero_7190_;
                } else {
                    v_one_7191_ = lean_unsigned_to_nat(1);
                    v_n_7192_ = lean_nat_sub(v_x_7188_, v_one_7191_);
                    lean_dec(v_x_7188_);
                    v___x_7193_ = lean_array_fget_borrowed(v_xs_7186_, v_n_7192_);
                    v___x_7194_ = lean_array_fget_borrowed(v_ys_7187_, v_n_7192_);
                    v___x_7195_ =
                        l_Lean_IR_Arg_alphaEqv(v_00_u03c1_7185_, v___x_7193_, v___x_7194_);
                    if v___x_7195_ == 0 {
                        lean_dec(v_n_7192_);
                        return v___x_7195_;
                    } else {
                        v_x_7188_ = v_n_7192_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg___boxed(
    mut v_00_u03c1_7197_: *mut LeanObject,
    mut v_xs_7198_: *mut LeanObject,
    mut v_ys_7199_: *mut LeanObject,
    mut v_x_7200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7201_: u8 = 0;
    let mut v_r_7202_: *mut LeanObject = core::ptr::null_mut();
    v_res_7201_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(
        v_00_u03c1_7197_,
        v_xs_7198_,
        v_ys_7199_,
        v_x_7200_,
    );
    lean_dec_ref(v_ys_7199_);
    lean_dec_ref(v_xs_7198_);
    lean_dec(v_00_u03c1_7197_);
    v_r_7202_ = lean_box((v_res_7201_) as usize);
    return v_r_7202_;
}
pub unsafe fn l_Lean_IR_args_alphaEqv(
    mut v_00_u03c1_7203_: *mut LeanObject,
    mut v_args_u2081_7204_: *mut LeanObject,
    mut v_args_u2082_7205_: *mut LeanObject,
) -> u8 {
    let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: u8 = 0;
    v___x_7206_ = lean_array_get_size(v_args_u2081_7204_);
    v___x_7207_ = lean_array_get_size(v_args_u2082_7205_);
    v___x_7208_ = lean_nat_dec_eq(v___x_7206_, v___x_7207_);
    if v___x_7208_ == 0 {
        return v___x_7208_;
    } else {
        let mut v___x_7209_: u8 = 0;
        v___x_7209_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(
            v_00_u03c1_7203_,
            v_args_u2081_7204_,
            v_args_u2082_7205_,
            v___x_7206_,
        );
        return v___x_7209_;
    }
}
pub unsafe fn l_Lean_IR_args_alphaEqv___boxed(
    mut v_00_u03c1_7210_: *mut LeanObject,
    mut v_args_u2081_7211_: *mut LeanObject,
    mut v_args_u2082_7212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7213_: u8 = 0;
    let mut v_r_7214_: *mut LeanObject = core::ptr::null_mut();
    v_res_7213_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_7210_, v_args_u2081_7211_, v_args_u2082_7212_);
    lean_dec_ref(v_args_u2082_7212_);
    lean_dec_ref(v_args_u2081_7211_);
    lean_dec(v_00_u03c1_7210_);
    v_r_7214_ = lean_box((v_res_7213_) as usize);
    return v_r_7214_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(
    mut v_00_u03c1_7215_: *mut LeanObject,
    mut v_xs_7216_: *mut LeanObject,
    mut v_ys_7217_: *mut LeanObject,
    mut v_hsz_7218_: *mut LeanObject,
    mut v_x_7219_: *mut LeanObject,
    mut v_x_7220_: *mut LeanObject,
) -> u8 {
    let mut v___x_7221_: u8 = 0;
    v___x_7221_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(
        v_00_u03c1_7215_,
        v_xs_7216_,
        v_ys_7217_,
        v_x_7219_,
    );
    return v___x_7221_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___boxed(
    mut v_00_u03c1_7222_: *mut LeanObject,
    mut v_xs_7223_: *mut LeanObject,
    mut v_ys_7224_: *mut LeanObject,
    mut v_hsz_7225_: *mut LeanObject,
    mut v_x_7226_: *mut LeanObject,
    mut v_x_7227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7228_: u8 = 0;
    let mut v_r_7229_: *mut LeanObject = core::ptr::null_mut();
    v_res_7228_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(
        v_00_u03c1_7222_,
        v_xs_7223_,
        v_ys_7224_,
        v_hsz_7225_,
        v_x_7226_,
        v_x_7227_,
    );
    lean_dec_ref(v_ys_7224_);
    lean_dec_ref(v_xs_7223_);
    lean_dec(v_00_u03c1_7222_);
    v_r_7229_ = lean_box((v_res_7228_) as usize);
    return v_r_7229_;
}
pub unsafe fn l_Lean_IR_Expr_alphaEqv(
    mut v_00_u03c1_7232_: *mut LeanObject,
    mut v_x_7233_: *mut LeanObject,
    mut v_x_7234_: *mut LeanObject,
) -> u8 {
    let mut v_n_u2081_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_u2081_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_u2082_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_u2082_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: u8 = 0;
    let mut v___x_7241_: u8 = 0;
    let mut v_c_u2081_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_u2081_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_u2082_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: u8 = 0;
    let mut v___x_7248_: u8 = 0;
    let mut v_i_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: u8 = 0;
    let mut v___x_7254_: u8 = 0;
    let mut v___x_7255_: u8 = 0;
    let mut v_n_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: u8 = 0;
    let mut v_x_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_7263_: u8 = 0;
    let mut v_ys_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_7267_: u8 = 0;
    let mut v_ys_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7270_: u8 = 0;
    let mut v___x_7271_: u8 = 0;
    let mut v___x_7272_: u8 = 0;
    let mut v___x_7273_: u8 = 0;
    let mut v___x_7274_: u8 = 0;
    let mut v___x_7275_: u8 = 0;
    let mut v_i_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: u8 = 0;
    let mut v_i_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: u8 = 0;
    let mut v_n_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7293_: u8 = 0;
    let mut v___x_7294_: u8 = 0;
    let mut v___x_7295_: u8 = 0;
    let mut v___x_7296_: u8 = 0;
    let mut v___x_7297_: u8 = 0;
    let mut v_c_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: u8 = 0;
    let mut v_c_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: u8 = 0;
    let mut v_x_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: u8 = 0;
    let mut v___x_7313_: u8 = 0;
    let mut v___x_7314_: u8 = 0;
    let mut v_ty_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_7317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: u8 = 0;
    let mut v___x_7320_: u8 = 0;
    let mut v___x_7321_: u8 = 0;
    let mut v_x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: u8 = 0;
    let mut v___x_7325_: u8 = 0;
    let mut v_v_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: u8 = 0;
    let mut v___x_7329_: u8 = 0;
    let mut v_x_7330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: u8 = 0;
    let mut v___x_7333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_7233_) {
                0 => {
                    if lean_obj_tag(v_x_7234_) == 0 {
                        v_i_7249_ = lean_ctor_get(v_x_7233_, 0);
                        v_ys_7250_ = lean_ctor_get(v_x_7233_, 1);
                        v_i_7251_ = lean_ctor_get(v_x_7234_, 0);
                        v_ys_7252_ = lean_ctor_get(v_x_7234_, 1);
                        v___x_7253_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_7249_, v_i_7251_);
                        if v___x_7253_ == 0 {
                            return v___x_7253_;
                        } else {
                            v___x_7254_ =
                                l_Lean_IR_args_alphaEqv(v_00_u03c1_7232_, v_ys_7250_, v_ys_7252_);
                            return v___x_7254_;
                        }
                    } else {
                        v___x_7255_ = 0;
                        return v___x_7255_;
                    }
                }
                1 => {
                    if lean_obj_tag(v_x_7234_) == 1 {
                        v_n_7256_ = lean_ctor_get(v_x_7233_, 0);
                        v_x_7257_ = lean_ctor_get(v_x_7233_, 1);
                        v_n_7258_ = lean_ctor_get(v_x_7234_, 0);
                        v_x_7259_ = lean_ctor_get(v_x_7234_, 1);
                        v_n_u2081_7236_ = v_n_7256_;
                        v_x_u2081_7237_ = v_x_7257_;
                        v_n_u2082_7238_ = v_n_7258_;
                        v_x_u2082_7239_ = v_x_7259_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7260_ = 0;
                        return v___x_7260_;
                    }
                }
                2 => {
                    if lean_obj_tag(v_x_7234_) == 2 {
                        v_x_7261_ = lean_ctor_get(v_x_7233_, 0);
                        v_i_7262_ = lean_ctor_get(v_x_7233_, 1);
                        v_updtHeader_7263_ = lean_ctor_get_uint8(
                            v_x_7233_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_ys_7264_ = lean_ctor_get(v_x_7233_, 2);
                        v_x_7265_ = lean_ctor_get(v_x_7234_, 0);
                        v_i_7266_ = lean_ctor_get(v_x_7234_, 1);
                        v_updtHeader_7267_ = lean_ctor_get_uint8(
                            v_x_7234_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_ys_7268_ = lean_ctor_get(v_x_7234_, 2);
                        v___x_7273_ =
                            l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7232_, v_x_7261_, v_x_7265_);
                        if v___x_7273_ == 0 {
                            v___y_7270_ = v___x_7273_;
                            state = 3;
                            continue;
                        } else {
                            v___x_7274_ = l_Lean_IR_instBEqCtorInfo_beq(v_i_7262_, v_i_7266_);
                            v___y_7270_ = v___x_7274_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_7275_ = 0;
                        return v___x_7275_;
                    }
                }
                3 => {
                    if lean_obj_tag(v_x_7234_) == 3 {
                        v_i_7276_ = lean_ctor_get(v_x_7233_, 0);
                        v_x_7277_ = lean_ctor_get(v_x_7233_, 1);
                        v_i_7278_ = lean_ctor_get(v_x_7234_, 0);
                        v_x_7279_ = lean_ctor_get(v_x_7234_, 1);
                        v_n_u2081_7236_ = v_i_7276_;
                        v_x_u2081_7237_ = v_x_7277_;
                        v_n_u2082_7238_ = v_i_7278_;
                        v_x_u2082_7239_ = v_x_7279_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7280_ = 0;
                        return v___x_7280_;
                    }
                }
                4 => {
                    if lean_obj_tag(v_x_7234_) == 4 {
                        v_i_7281_ = lean_ctor_get(v_x_7233_, 0);
                        v_x_7282_ = lean_ctor_get(v_x_7233_, 1);
                        v_i_7283_ = lean_ctor_get(v_x_7234_, 0);
                        v_x_7284_ = lean_ctor_get(v_x_7234_, 1);
                        v_n_u2081_7236_ = v_i_7281_;
                        v_x_u2081_7237_ = v_x_7282_;
                        v_n_u2082_7238_ = v_i_7283_;
                        v_x_u2082_7239_ = v_x_7284_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7285_ = 0;
                        return v___x_7285_;
                    }
                }
                5 => {
                    if lean_obj_tag(v_x_7234_) == 5 {
                        v_n_7286_ = lean_ctor_get(v_x_7233_, 0);
                        v_offset_7287_ = lean_ctor_get(v_x_7233_, 1);
                        v_x_7288_ = lean_ctor_get(v_x_7233_, 2);
                        v_n_7289_ = lean_ctor_get(v_x_7234_, 0);
                        v_offset_7290_ = lean_ctor_get(v_x_7234_, 1);
                        v_x_7291_ = lean_ctor_get(v_x_7234_, 2);
                        v___x_7295_ = lean_nat_dec_eq(v_n_7286_, v_n_7289_);
                        if v___x_7295_ == 0 {
                            v___y_7293_ = v___x_7295_;
                            state = 4;
                            continue;
                        } else {
                            v___x_7296_ = lean_nat_dec_eq(v_offset_7287_, v_offset_7290_);
                            v___y_7293_ = v___x_7296_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_7297_ = 0;
                        return v___x_7297_;
                    }
                }
                6 => {
                    if lean_obj_tag(v_x_7234_) == 6 {
                        v_c_7298_ = lean_ctor_get(v_x_7233_, 0);
                        v_ys_7299_ = lean_ctor_get(v_x_7233_, 1);
                        v_c_7300_ = lean_ctor_get(v_x_7234_, 0);
                        v_ys_7301_ = lean_ctor_get(v_x_7234_, 1);
                        v_c_u2081_7243_ = v_c_7298_;
                        v_ys_u2081_7244_ = v_ys_7299_;
                        v_c_u2082_7245_ = v_c_7300_;
                        v_ys_u2082_7246_ = v_ys_7301_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7302_ = 0;
                        return v___x_7302_;
                    }
                }
                7 => {
                    if lean_obj_tag(v_x_7234_) == 7 {
                        v_c_7303_ = lean_ctor_get(v_x_7233_, 0);
                        v_ys_7304_ = lean_ctor_get(v_x_7233_, 1);
                        v_c_7305_ = lean_ctor_get(v_x_7234_, 0);
                        v_ys_7306_ = lean_ctor_get(v_x_7234_, 1);
                        v_c_u2081_7243_ = v_c_7303_;
                        v_ys_u2081_7244_ = v_ys_7304_;
                        v_c_u2082_7245_ = v_c_7305_;
                        v_ys_u2082_7246_ = v_ys_7306_;
                        state = 2;
                        continue;
                    } else {
                        v___x_7307_ = 0;
                        return v___x_7307_;
                    }
                }
                8 => {
                    if lean_obj_tag(v_x_7234_) == 8 {
                        v_x_7308_ = lean_ctor_get(v_x_7233_, 0);
                        v_ys_7309_ = lean_ctor_get(v_x_7233_, 1);
                        v_x_7310_ = lean_ctor_get(v_x_7234_, 0);
                        v_ys_7311_ = lean_ctor_get(v_x_7234_, 1);
                        v___x_7312_ =
                            l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7232_, v_x_7308_, v_x_7310_);
                        if v___x_7312_ == 0 {
                            return v___x_7312_;
                        } else {
                            v___x_7313_ =
                                l_Lean_IR_args_alphaEqv(v_00_u03c1_7232_, v_ys_7309_, v_ys_7311_);
                            return v___x_7313_;
                        }
                    } else {
                        v___x_7314_ = 0;
                        return v___x_7314_;
                    }
                }
                9 => {
                    if lean_obj_tag(v_x_7234_) == 9 {
                        v_ty_7315_ = lean_ctor_get(v_x_7233_, 0);
                        v_x_7316_ = lean_ctor_get(v_x_7233_, 1);
                        v_ty_7317_ = lean_ctor_get(v_x_7234_, 0);
                        v_x_7318_ = lean_ctor_get(v_x_7234_, 1);
                        v___x_7319_ = l_Lean_IR_instBEqIRType_beq(v_ty_7315_, v_ty_7317_);
                        if v___x_7319_ == 0 {
                            return v___x_7319_;
                        } else {
                            v___x_7320_ =
                                l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7232_, v_x_7316_, v_x_7318_);
                            return v___x_7320_;
                        }
                    } else {
                        v___x_7321_ = 0;
                        return v___x_7321_;
                    }
                }
                10 => {
                    if lean_obj_tag(v_x_7234_) == 10 {
                        v_x_7322_ = lean_ctor_get(v_x_7233_, 0);
                        v_x_7323_ = lean_ctor_get(v_x_7234_, 0);
                        v___x_7324_ =
                            l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7232_, v_x_7322_, v_x_7323_);
                        return v___x_7324_;
                    } else {
                        v___x_7325_ = 0;
                        return v___x_7325_;
                    }
                }
                11 => {
                    if lean_obj_tag(v_x_7234_) == 11 {
                        v_v_7326_ = lean_ctor_get(v_x_7233_, 0);
                        v_v_7327_ = lean_ctor_get(v_x_7234_, 0);
                        v___x_7328_ = l_Lean_IR_instBEqLitVal_beq(v_v_7326_, v_v_7327_);
                        return v___x_7328_;
                    } else {
                        v___x_7329_ = 0;
                        return v___x_7329_;
                    }
                }
                _ => {
                    if lean_obj_tag(v_x_7234_) == 12 {
                        v_x_7330_ = lean_ctor_get(v_x_7233_, 0);
                        v_x_7331_ = lean_ctor_get(v_x_7234_, 0);
                        v___x_7332_ =
                            l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7232_, v_x_7330_, v_x_7331_);
                        return v___x_7332_;
                    } else {
                        v___x_7333_ = 0;
                        return v___x_7333_;
                    }
                }
            },
            1 => {
                v___x_7240_ = lean_nat_dec_eq(v_n_u2081_7236_, v_n_u2082_7238_);
                if v___x_7240_ == 0 {
                    return v___x_7240_;
                } else {
                    v___x_7241_ = l_Lean_IR_VarId_alphaEqv(
                        v_00_u03c1_7232_,
                        v_x_u2081_7237_,
                        v_x_u2082_7239_,
                    );
                    return v___x_7241_;
                }
            }
            2 => {
                v___x_7247_ = lean_name_eq(v_c_u2081_7243_, v_c_u2082_7245_);
                if v___x_7247_ == 0 {
                    return v___x_7247_;
                } else {
                    v___x_7248_ = l_Lean_IR_args_alphaEqv(
                        v_00_u03c1_7232_,
                        v_ys_u2081_7244_,
                        v_ys_u2082_7246_,
                    );
                    return v___x_7248_;
                }
            }
            3 => {
                if v___y_7270_ == 0 {
                    return v___y_7270_;
                } else {
                    if v_updtHeader_7263_ == 0 {
                        if v_updtHeader_7267_ == 0 {
                            v___x_7271_ =
                                l_Lean_IR_args_alphaEqv(v_00_u03c1_7232_, v_ys_7264_, v_ys_7268_);
                            return v___x_7271_;
                        } else {
                            return v_updtHeader_7263_;
                        }
                    } else {
                        if v_updtHeader_7267_ == 0 {
                            return v_updtHeader_7267_;
                        } else {
                            v___x_7272_ =
                                l_Lean_IR_args_alphaEqv(v_00_u03c1_7232_, v_ys_7264_, v_ys_7268_);
                            return v___x_7272_;
                        }
                    }
                }
            }
            4 => {
                if v___y_7293_ == 0 {
                    return v___y_7293_;
                } else {
                    v___x_7294_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7232_, v_x_7288_, v_x_7291_);
                    return v___x_7294_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Expr_alphaEqv___boxed(
    mut v_00_u03c1_7334_: *mut LeanObject,
    mut v_x_7335_: *mut LeanObject,
    mut v_x_7336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7337_: u8 = 0;
    let mut v_r_7338_: *mut LeanObject = core::ptr::null_mut();
    v_res_7337_ = l_Lean_IR_Expr_alphaEqv(v_00_u03c1_7334_, v_x_7335_, v_x_7336_);
    lean_dec_ref(v_x_7336_);
    lean_dec_ref(v_x_7335_);
    lean_dec(v_00_u03c1_7334_);
    v_r_7338_ = lean_box((v_res_7337_) as usize);
    return v_r_7338_;
}
pub unsafe fn l_Lean_IR_addVarRename(
    mut v_00_u03c1_7341_: *mut LeanObject,
    mut v_x_u2081_7342_: *mut LeanObject,
    mut v_x_u2082_7343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7344_: u8 = 0;
    v___x_7344_ = lean_nat_dec_eq(v_x_u2081_7342_, v_x_u2082_7343_);
    if v___x_7344_ == 0 {
        let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
        v___x_7345_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
                v_x_u2081_7342_,
                v_x_u2082_7343_,
                v_00_u03c1_7341_,
            );
        return v___x_7345_;
    } else {
        lean_dec(v_x_u2082_7343_);
        lean_dec(v_x_u2081_7342_);
        return v_00_u03c1_7341_;
    }
}
pub unsafe fn l_Lean_IR_addParamRename(
    mut v_00_u03c1_7346_: *mut LeanObject,
    mut v_p_u2081_7347_: *mut LeanObject,
    mut v_p_u2082_7348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_7350_: u8 = 0;
    let mut v_ty_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_borrow_7353_: u8 = 0;
    let mut v_ty_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7356_: u8 = 0;
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: u8 = 0;
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_7349_ = lean_ctor_get(v_p_u2081_7347_, 0);
                lean_inc(v_x_7349_);
                v_borrow_7350_ = lean_ctor_get_uint8(
                    v_p_u2081_7347_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_ty_7351_ = lean_ctor_get(v_p_u2081_7347_, 1);
                lean_inc(v_ty_7351_);
                lean_dec_ref(v_p_u2081_7347_);
                v_x_7352_ = lean_ctor_get(v_p_u2082_7348_, 0);
                lean_inc(v_x_7352_);
                v_borrow_7353_ = lean_ctor_get_uint8(
                    v_p_u2082_7348_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_ty_7354_ = lean_ctor_get(v_p_u2082_7348_, 1);
                lean_inc(v_ty_7354_);
                lean_dec_ref(v_p_u2082_7348_);
                v___x_7360_ = l_Lean_IR_instBEqIRType_beq(v_ty_7351_, v_ty_7354_);
                lean_dec(v_ty_7354_);
                lean_dec(v_ty_7351_);
                if v___x_7360_ == 0 {
                    v___y_7356_ = v___x_7360_;
                    state = 1;
                    continue;
                } else {
                    if v_borrow_7350_ == 0 {
                        if v_borrow_7353_ == 0 {
                            v___y_7356_ = v___x_7360_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_7352_);
                            lean_dec(v_x_7349_);
                            lean_dec(v_00_u03c1_7346_);
                            v___x_7361_ = lean_box(0);
                            return v___x_7361_;
                        }
                    } else {
                        v___y_7356_ = v_borrow_7353_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_7356_ == 0 {
                    lean_dec(v_x_7352_);
                    lean_dec(v_x_7349_);
                    lean_dec(v_00_u03c1_7346_);
                    v___x_7357_ = lean_box(0);
                    return v___x_7357_;
                } else {
                    v___x_7358_ = l_Lean_IR_addVarRename(v_00_u03c1_7346_, v_x_7349_, v_x_7352_);
                    v___x_7359_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7359_, 0, v___x_7358_);
                    return v___x_7359_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(
    mut v_upperBound_7362_: *mut LeanObject,
    mut v_ps_u2081_7363_: *mut LeanObject,
    mut v_ps_u2082_7364_: *mut LeanObject,
    mut v_a_7365_: *mut LeanObject,
    mut v_b_7366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7367_: u8 = 0;
    let mut v___x_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7367_ = lean_nat_dec_lt(v_a_7365_, v_upperBound_7362_);
                if v___x_7367_ == 0 {
                    lean_dec(v_a_7365_);
                    v___x_7368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7368_, 0, v_b_7366_);
                    return v___x_7368_;
                } else {
                    v___x_7369_ = l_Lean_IR_instInhabitedParam_default;
                    v___x_7370_ = lean_array_get_borrowed(v___x_7369_, v_ps_u2081_7363_, v_a_7365_);
                    v___x_7371_ = lean_array_get_borrowed(v___x_7369_, v_ps_u2082_7364_, v_a_7365_);
                    lean_inc(v___x_7371_);
                    lean_inc(v___x_7370_);
                    v___x_7372_ = l_Lean_IR_addParamRename(v_b_7366_, v___x_7370_, v___x_7371_);
                    if lean_obj_tag(v___x_7372_) == 0 {
                        lean_dec(v_a_7365_);
                        return v___x_7372_;
                    } else {
                        v_val_7373_ = lean_ctor_get(v___x_7372_, 0);
                        lean_inc(v_val_7373_);
                        lean_dec_ref_known(v___x_7372_, 1);
                        v___x_7374_ = lean_unsigned_to_nat(1);
                        v___x_7375_ = lean_nat_add(v_a_7365_, v___x_7374_);
                        lean_dec(v_a_7365_);
                        v_a_7365_ = v___x_7375_;
                        v_b_7366_ = v_val_7373_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg___boxed(
    mut v_upperBound_7377_: *mut LeanObject,
    mut v_ps_u2081_7378_: *mut LeanObject,
    mut v_ps_u2082_7379_: *mut LeanObject,
    mut v_a_7380_: *mut LeanObject,
    mut v_b_7381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7382_: *mut LeanObject = core::ptr::null_mut();
    v_res_7382_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(
        v_upperBound_7377_,
        v_ps_u2081_7378_,
        v_ps_u2082_7379_,
        v_a_7380_,
        v_b_7381_,
    );
    lean_dec_ref(v_ps_u2082_7379_);
    lean_dec_ref(v_ps_u2081_7378_);
    lean_dec(v_upperBound_7377_);
    return v_res_7382_;
}
pub unsafe fn l_Lean_IR_addParamsRename(
    mut v_00_u03c1_7383_: *mut LeanObject,
    mut v_ps_u2081_7384_: *mut LeanObject,
    mut v_ps_u2082_7385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: u8 = 0;
    v___x_7386_ = lean_array_get_size(v_ps_u2081_7384_);
    v___x_7387_ = lean_array_get_size(v_ps_u2082_7385_);
    v___x_7388_ = lean_nat_dec_eq(v___x_7386_, v___x_7387_);
    if v___x_7388_ == 0 {
        let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_00_u03c1_7383_);
        v___x_7389_ = lean_box(0);
        return v___x_7389_;
    } else {
        let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
        v___x_7390_ = lean_unsigned_to_nat(0);
        v___x_7391_ =
            l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(
                v___x_7386_,
                v_ps_u2081_7384_,
                v_ps_u2082_7385_,
                v___x_7390_,
                v_00_u03c1_7383_,
            );
        return v___x_7391_;
    }
}
pub unsafe fn l_Lean_IR_addParamsRename___boxed(
    mut v_00_u03c1_7392_: *mut LeanObject,
    mut v_ps_u2081_7393_: *mut LeanObject,
    mut v_ps_u2082_7394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7395_: *mut LeanObject = core::ptr::null_mut();
    v_res_7395_ = l_Lean_IR_addParamsRename(v_00_u03c1_7392_, v_ps_u2081_7393_, v_ps_u2082_7394_);
    lean_dec_ref(v_ps_u2082_7394_);
    lean_dec_ref(v_ps_u2081_7393_);
    return v_res_7395_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(
    mut v_upperBound_7396_: *mut LeanObject,
    mut v_ps_u2081_7397_: *mut LeanObject,
    mut v_ps_u2082_7398_: *mut LeanObject,
    mut v_inst_7399_: *mut LeanObject,
    mut v_R_7400_: *mut LeanObject,
    mut v_a_7401_: *mut LeanObject,
    mut v_b_7402_: *mut LeanObject,
    mut v_c_7403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7404_: *mut LeanObject = core::ptr::null_mut();
    v___x_7404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(
        v_upperBound_7396_,
        v_ps_u2081_7397_,
        v_ps_u2082_7398_,
        v_a_7401_,
        v_b_7402_,
    );
    return v___x_7404_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___boxed(
    mut v_upperBound_7405_: *mut LeanObject,
    mut v_ps_u2081_7406_: *mut LeanObject,
    mut v_ps_u2082_7407_: *mut LeanObject,
    mut v_inst_7408_: *mut LeanObject,
    mut v_R_7409_: *mut LeanObject,
    mut v_a_7410_: *mut LeanObject,
    mut v_b_7411_: *mut LeanObject,
    mut v_c_7412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7413_: *mut LeanObject = core::ptr::null_mut();
    v_res_7413_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(
        v_upperBound_7405_,
        v_ps_u2081_7406_,
        v_ps_u2082_7407_,
        v_inst_7408_,
        v_R_7409_,
        v_a_7410_,
        v_b_7411_,
        v_c_7412_,
    );
    lean_dec_ref(v_ps_u2082_7407_);
    lean_dec_ref(v_ps_u2081_7406_);
    lean_dec(v_upperBound_7405_);
    return v_res_7413_;
}
pub unsafe fn l_Lean_IR_FnBody_alphaEqv(
    mut v_x_7414_: *mut LeanObject,
    mut v_x_7415_: *mut LeanObject,
    mut v_x_7416_: *mut LeanObject,
) -> u8 {
    let mut v___y_7418_: u8 = 0;
    let mut v___y_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7421_: u8 = 0;
    let mut v___y_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7426_: u8 = 0;
    let mut v___y_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7429_: u8 = 0;
    let mut v___y_7430_: u8 = 0;
    let mut v___y_7431_: u8 = 0;
    let mut v___y_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7433_: u8 = 0;
    let mut v_00_u03c1_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_u2081_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_u2081_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_7438_: u8 = 0;
    let mut v_p_u2081_7439_: u8 = 0;
    let mut v_b_u2081_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_u2082_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_u2082_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_7443_: u8 = 0;
    let mut v_p_u2082_7444_: u8 = 0;
    let mut v_b_u2082_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: u8 = 0;
    let mut v___x_7447_: u8 = 0;
    let mut v_x_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_7453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7457_: u8 = 0;
    let mut v___x_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: u8 = 0;
    let mut v___x_7462_: u8 = 0;
    let mut v_j_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: u8 = 0;
    let mut v_val_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7474_: u8 = 0;
    let mut v___x_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: u8 = 0;
    let mut v_x_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7487_: u8 = 0;
    let mut v___x_7488_: u8 = 0;
    let mut v___x_7490_: u8 = 0;
    let mut v___x_7491_: u8 = 0;
    let mut v___x_7492_: u8 = 0;
    let mut v_x_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_7494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cidx_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7500_: u8 = 0;
    let mut v___x_7502_: u8 = 0;
    let mut v___x_7503_: u8 = 0;
    let mut v___x_7504_: u8 = 0;
    let mut v_x_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7514_: u8 = 0;
    let mut v___x_7515_: u8 = 0;
    let mut v___x_7517_: u8 = 0;
    let mut v___x_7518_: u8 = 0;
    let mut v___x_7519_: u8 = 0;
    let mut v_x_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: u8 = 0;
    let mut v___y_7534_: u8 = 0;
    let mut v___x_7535_: u8 = 0;
    let mut v___x_7536_: u8 = 0;
    let mut v___x_7538_: u8 = 0;
    let mut v___x_7539_: u8 = 0;
    let mut v___x_7540_: u8 = 0;
    let mut v_x_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7543_: u8 = 0;
    let mut v_persistent_7544_: u8 = 0;
    let mut v_b_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7548_: u8 = 0;
    let mut v_persistent_7549_: u8 = 0;
    let mut v_b_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: u8 = 0;
    let mut v_x_7552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7554_: u8 = 0;
    let mut v_persistent_7555_: u8 = 0;
    let mut v_b_7556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_7559_: u8 = 0;
    let mut v_persistent_7560_: u8 = 0;
    let mut v_b_7561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: u8 = 0;
    let mut v_x_7563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: u8 = 0;
    let mut v___x_7569_: u8 = 0;
    let mut v_tid_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tid_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cs_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7577_: u8 = 0;
    let mut v___x_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: u8 = 0;
    let mut v___x_7581_: u8 = 0;
    let mut v___x_7582_: u8 = 0;
    let mut v___x_7583_: u8 = 0;
    let mut v___x_7584_: u8 = 0;
    let mut v_x_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: u8 = 0;
    let mut v___x_7588_: u8 = 0;
    let mut v_j_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_j_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_7592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: u8 = 0;
    let mut v___x_7594_: u8 = 0;
    let mut v___x_7595_: u8 = 0;
    let mut v___x_7596_: u8 = 0;
    let mut v___x_7597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_7415_) {
                0 => {
                    if lean_obj_tag(v_x_7416_) == 0 {
                        v_x_7448_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7448_);
                        v_ty_7449_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_ty_7449_);
                        v_e_7450_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc_ref(v_e_7450_);
                        v_b_7451_ = lean_ctor_get(v_x_7415_, 3);
                        lean_inc(v_b_7451_);
                        lean_dec_ref_known(v_x_7415_, 4);
                        v_x_7452_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7452_);
                        v_ty_7453_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_ty_7453_);
                        v_e_7454_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc_ref(v_e_7454_);
                        v_b_7455_ = lean_ctor_get(v_x_7416_, 3);
                        lean_inc(v_b_7455_);
                        lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7460_ = l_Lean_IR_instBEqIRType_beq(v_ty_7449_, v_ty_7453_);
                        lean_dec(v_ty_7453_);
                        lean_dec(v_ty_7449_);
                        if v___x_7460_ == 0 {
                            lean_dec_ref(v_e_7454_);
                            lean_dec_ref(v_e_7450_);
                            v___y_7457_ = v___x_7460_;
                            state = 4;
                            continue;
                        } else {
                            v___x_7461_ = l_Lean_IR_Expr_alphaEqv(v_x_7414_, v_e_7450_, v_e_7454_);
                            lean_dec_ref(v_e_7454_);
                            lean_dec_ref(v_e_7450_);
                            v___y_7457_ = v___x_7461_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 4);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7462_ = 0;
                        return v___x_7462_;
                    }
                }
                1 => {
                    if lean_obj_tag(v_x_7416_) == 1 {
                        v_j_7463_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_j_7463_);
                        v_xs_7464_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc_ref(v_xs_7464_);
                        v_v_7465_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc(v_v_7465_);
                        v_b_7466_ = lean_ctor_get(v_x_7415_, 3);
                        lean_inc(v_b_7466_);
                        lean_dec_ref_known(v_x_7415_, 4);
                        v_j_7467_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_j_7467_);
                        v_xs_7468_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc_ref(v_xs_7468_);
                        v_v_7469_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc(v_v_7469_);
                        v_b_7470_ = lean_ctor_get(v_x_7416_, 3);
                        lean_inc(v_b_7470_);
                        lean_dec_ref_known(v_x_7416_, 4);
                        lean_inc(v_x_7414_);
                        v___x_7471_ = l_Lean_IR_addParamsRename(v_x_7414_, v_xs_7464_, v_xs_7468_);
                        lean_dec_ref(v_xs_7468_);
                        lean_dec_ref(v_xs_7464_);
                        if lean_obj_tag(v___x_7471_) == 0 {
                            lean_dec(v_b_7470_);
                            lean_dec(v_v_7469_);
                            lean_dec(v_j_7467_);
                            lean_dec(v_b_7466_);
                            lean_dec(v_v_7465_);
                            lean_dec(v_j_7463_);
                            lean_dec(v_x_7414_);
                            v___x_7472_ = 0;
                            return v___x_7472_;
                        } else {
                            v_val_7473_ = lean_ctor_get(v___x_7471_, 0);
                            lean_inc(v_val_7473_);
                            lean_dec_ref_known(v___x_7471_, 1);
                            v___x_7474_ =
                                l_Lean_IR_FnBody_alphaEqv(v_val_7473_, v_v_7465_, v_v_7469_);
                            if v___x_7474_ == 0 {
                                lean_dec(v_b_7470_);
                                lean_dec(v_j_7467_);
                                lean_dec(v_b_7466_);
                                lean_dec(v_j_7463_);
                                lean_dec(v_x_7414_);
                                return v___x_7474_;
                            } else {
                                v___x_7475_ =
                                    l_Lean_IR_addVarRename(v_x_7414_, v_j_7463_, v_j_7467_);
                                v_x_7414_ = v___x_7475_;
                                v_x_7415_ = v_b_7466_;
                                v_x_7416_ = v_b_7470_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 4);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7477_ = 0;
                        return v___x_7477_;
                    }
                }
                2 => {
                    if lean_obj_tag(v_x_7416_) == 2 {
                        v_x_7478_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7478_);
                        v_i_7479_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_i_7479_);
                        v_y_7480_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc(v_y_7480_);
                        v_b_7481_ = lean_ctor_get(v_x_7415_, 3);
                        lean_inc(v_b_7481_);
                        lean_dec_ref_known(v_x_7415_, 4);
                        v_x_7482_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7482_);
                        v_i_7483_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_i_7483_);
                        v_y_7484_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc(v_y_7484_);
                        v_b_7485_ = lean_ctor_get(v_x_7416_, 3);
                        lean_inc(v_b_7485_);
                        lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7490_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7478_, v_x_7482_);
                        lean_dec(v_x_7482_);
                        lean_dec(v_x_7478_);
                        if v___x_7490_ == 0 {
                            lean_dec(v_i_7483_);
                            lean_dec(v_i_7479_);
                            v___y_7487_ = v___x_7490_;
                            state = 5;
                            continue;
                        } else {
                            v___x_7491_ = lean_nat_dec_eq(v_i_7479_, v_i_7483_);
                            lean_dec(v_i_7483_);
                            lean_dec(v_i_7479_);
                            v___y_7487_ = v___x_7491_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 4);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7492_ = 0;
                        return v___x_7492_;
                    }
                }
                3 => {
                    if lean_obj_tag(v_x_7416_) == 3 {
                        v_x_7493_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7493_);
                        v_cidx_7494_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_cidx_7494_);
                        v_b_7495_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc(v_b_7495_);
                        lean_dec_ref_known(v_x_7415_, 3);
                        v_x_7496_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7496_);
                        v_cidx_7497_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_cidx_7497_);
                        v_b_7498_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc(v_b_7498_);
                        lean_dec_ref_known(v_x_7416_, 3);
                        v___x_7502_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7493_, v_x_7496_);
                        lean_dec(v_x_7496_);
                        lean_dec(v_x_7493_);
                        if v___x_7502_ == 0 {
                            lean_dec(v_cidx_7497_);
                            lean_dec(v_cidx_7494_);
                            v___y_7500_ = v___x_7502_;
                            state = 6;
                            continue;
                        } else {
                            v___x_7503_ = lean_nat_dec_eq(v_cidx_7494_, v_cidx_7497_);
                            lean_dec(v_cidx_7497_);
                            lean_dec(v_cidx_7494_);
                            v___y_7500_ = v___x_7503_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 3);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7504_ = 0;
                        return v___x_7504_;
                    }
                }
                4 => {
                    if lean_obj_tag(v_x_7416_) == 4 {
                        v_x_7505_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7505_);
                        v_i_7506_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_i_7506_);
                        v_y_7507_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc(v_y_7507_);
                        v_b_7508_ = lean_ctor_get(v_x_7415_, 3);
                        lean_inc(v_b_7508_);
                        lean_dec_ref_known(v_x_7415_, 4);
                        v_x_7509_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7509_);
                        v_i_7510_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_i_7510_);
                        v_y_7511_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc(v_y_7511_);
                        v_b_7512_ = lean_ctor_get(v_x_7416_, 3);
                        lean_inc(v_b_7512_);
                        lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7517_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7505_, v_x_7509_);
                        lean_dec(v_x_7509_);
                        lean_dec(v_x_7505_);
                        if v___x_7517_ == 0 {
                            lean_dec(v_i_7510_);
                            lean_dec(v_i_7506_);
                            v___y_7514_ = v___x_7517_;
                            state = 7;
                            continue;
                        } else {
                            v___x_7518_ = lean_nat_dec_eq(v_i_7506_, v_i_7510_);
                            lean_dec(v_i_7510_);
                            lean_dec(v_i_7506_);
                            v___y_7514_ = v___x_7518_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 4);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7519_ = 0;
                        return v___x_7519_;
                    }
                }
                5 => {
                    if lean_obj_tag(v_x_7416_) == 5 {
                        v_x_7520_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7520_);
                        v_i_7521_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_i_7521_);
                        v_offset_7522_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc(v_offset_7522_);
                        v_y_7523_ = lean_ctor_get(v_x_7415_, 3);
                        lean_inc(v_y_7523_);
                        v_ty_7524_ = lean_ctor_get(v_x_7415_, 4);
                        lean_inc(v_ty_7524_);
                        v_b_7525_ = lean_ctor_get(v_x_7415_, 5);
                        lean_inc(v_b_7525_);
                        lean_dec_ref_known(v_x_7415_, 6);
                        v_x_7526_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7526_);
                        v_i_7527_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_i_7527_);
                        v_offset_7528_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc(v_offset_7528_);
                        v_y_7529_ = lean_ctor_get(v_x_7416_, 3);
                        lean_inc(v_y_7529_);
                        v_ty_7530_ = lean_ctor_get(v_x_7416_, 4);
                        lean_inc(v_ty_7530_);
                        v_b_7531_ = lean_ctor_get(v_x_7416_, 5);
                        lean_inc(v_b_7531_);
                        lean_dec_ref_known(v_x_7416_, 6);
                        v___x_7532_ = lean_nat_dec_eq(v_offset_7522_, v_offset_7528_);
                        lean_dec(v_offset_7528_);
                        lean_dec(v_offset_7522_);
                        v___x_7538_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7520_, v_x_7526_);
                        lean_dec(v_x_7526_);
                        lean_dec(v_x_7520_);
                        if v___x_7538_ == 0 {
                            lean_dec(v_i_7527_);
                            lean_dec(v_i_7521_);
                            v___y_7534_ = v___x_7538_;
                            state = 8;
                            continue;
                        } else {
                            v___x_7539_ = lean_nat_dec_eq(v_i_7521_, v_i_7527_);
                            lean_dec(v_i_7527_);
                            lean_dec(v_i_7521_);
                            v___y_7534_ = v___x_7539_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 6);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7540_ = 0;
                        return v___x_7540_;
                    }
                }
                6 => {
                    if lean_obj_tag(v_x_7416_) == 6 {
                        v_x_7541_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7541_);
                        v_n_7542_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_n_7542_);
                        v_c_7543_ = lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_persistent_7544_ = lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7545_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc(v_b_7545_);
                        lean_dec_ref_known(v_x_7415_, 3);
                        v_x_7546_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7546_);
                        v_n_7547_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_n_7547_);
                        v_c_7548_ = lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_persistent_7549_ = lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7550_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc(v_b_7550_);
                        lean_dec_ref_known(v_x_7416_, 3);
                        v_00_u03c1_7435_ = v_x_7414_;
                        v_x_u2081_7436_ = v_x_7541_;
                        v_n_u2081_7437_ = v_n_7542_;
                        v_c_u2081_7438_ = v_c_7543_;
                        v_p_u2081_7439_ = v_persistent_7544_;
                        v_b_u2081_7440_ = v_b_7545_;
                        v_x_u2082_7441_ = v_x_7546_;
                        v_n_u2082_7442_ = v_n_7547_;
                        v_c_u2082_7443_ = v_c_7548_;
                        v_p_u2082_7444_ = v_persistent_7549_;
                        v_b_u2082_7445_ = v_b_7550_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref_known(v_x_7415_, 3);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7551_ = 0;
                        return v___x_7551_;
                    }
                }
                7 => {
                    if lean_obj_tag(v_x_7416_) == 7 {
                        v_x_7552_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7552_);
                        v_n_7553_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_n_7553_);
                        v_c_7554_ = lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_persistent_7555_ = lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7556_ = lean_ctor_get(v_x_7415_, 2);
                        lean_inc(v_b_7556_);
                        lean_dec_ref_known(v_x_7415_, 3);
                        v_x_7557_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7557_);
                        v_n_7558_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_n_7558_);
                        v_c_7559_ = lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        );
                        v_persistent_7560_ = lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7561_ = lean_ctor_get(v_x_7416_, 2);
                        lean_inc(v_b_7561_);
                        lean_dec_ref_known(v_x_7416_, 3);
                        v_00_u03c1_7435_ = v_x_7414_;
                        v_x_u2081_7436_ = v_x_7552_;
                        v_n_u2081_7437_ = v_n_7553_;
                        v_c_u2081_7438_ = v_c_7554_;
                        v_p_u2081_7439_ = v_persistent_7555_;
                        v_b_u2081_7440_ = v_b_7556_;
                        v_x_u2082_7441_ = v_x_7557_;
                        v_n_u2082_7442_ = v_n_7558_;
                        v_c_u2082_7443_ = v_c_7559_;
                        v_p_u2082_7444_ = v_persistent_7560_;
                        v_b_u2082_7445_ = v_b_7561_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref_known(v_x_7415_, 3);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7562_ = 0;
                        return v___x_7562_;
                    }
                }
                8 => {
                    if lean_obj_tag(v_x_7416_) == 8 {
                        v_x_7563_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7563_);
                        v_b_7564_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_b_7564_);
                        lean_dec_ref_known(v_x_7415_, 2);
                        v_x_7565_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7565_);
                        v_b_7566_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_b_7566_);
                        lean_dec_ref_known(v_x_7416_, 2);
                        v___x_7567_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7563_, v_x_7565_);
                        lean_dec(v_x_7565_);
                        lean_dec(v_x_7563_);
                        if v___x_7567_ == 0 {
                            lean_dec(v_b_7566_);
                            lean_dec(v_b_7564_);
                            lean_dec(v_x_7414_);
                            return v___x_7567_;
                        } else {
                            v_x_7415_ = v_b_7564_;
                            v_x_7416_ = v_b_7566_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 2);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7569_ = 0;
                        return v___x_7569_;
                    }
                }
                9 => {
                    if lean_obj_tag(v_x_7416_) == 9 {
                        v_tid_7570_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_tid_7570_);
                        v_x_7571_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc(v_x_7571_);
                        v_cs_7572_ = lean_ctor_get(v_x_7415_, 3);
                        lean_inc_ref(v_cs_7572_);
                        lean_dec_ref_known(v_x_7415_, 4);
                        v_tid_7573_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_tid_7573_);
                        v_x_7574_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc(v_x_7574_);
                        v_cs_7575_ = lean_ctor_get(v_x_7416_, 3);
                        lean_inc_ref(v_cs_7575_);
                        lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7582_ = lean_name_eq(v_tid_7570_, v_tid_7573_);
                        lean_dec(v_tid_7573_);
                        lean_dec(v_tid_7570_);
                        if v___x_7582_ == 0 {
                            lean_dec(v_x_7574_);
                            lean_dec(v_x_7571_);
                            v___y_7577_ = v___x_7582_;
                            state = 9;
                            continue;
                        } else {
                            v___x_7583_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7571_, v_x_7574_);
                            lean_dec(v_x_7574_);
                            lean_dec(v_x_7571_);
                            v___y_7577_ = v___x_7583_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 4);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7584_ = 0;
                        return v___x_7584_;
                    }
                }
                10 => {
                    if lean_obj_tag(v_x_7416_) == 10 {
                        v_x_7585_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_x_7585_);
                        lean_dec_ref_known(v_x_7415_, 1);
                        v_x_7586_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_x_7586_);
                        lean_dec_ref_known(v_x_7416_, 1);
                        v___x_7587_ = l_Lean_IR_Arg_alphaEqv(v_x_7414_, v_x_7585_, v_x_7586_);
                        lean_dec(v_x_7586_);
                        lean_dec(v_x_7585_);
                        lean_dec(v_x_7414_);
                        return v___x_7587_;
                    } else {
                        lean_dec_ref_known(v_x_7415_, 1);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7588_ = 0;
                        return v___x_7588_;
                    }
                }
                11 => {
                    if lean_obj_tag(v_x_7416_) == 11 {
                        v_j_7589_ = lean_ctor_get(v_x_7415_, 0);
                        lean_inc(v_j_7589_);
                        v_ys_7590_ = lean_ctor_get(v_x_7415_, 1);
                        lean_inc_ref(v_ys_7590_);
                        lean_dec_ref_known(v_x_7415_, 2);
                        v_j_7591_ = lean_ctor_get(v_x_7416_, 0);
                        lean_inc(v_j_7591_);
                        v_ys_7592_ = lean_ctor_get(v_x_7416_, 1);
                        lean_inc_ref(v_ys_7592_);
                        lean_dec_ref_known(v_x_7416_, 2);
                        v___x_7593_ = lean_nat_dec_eq(v_j_7589_, v_j_7591_);
                        lean_dec(v_j_7591_);
                        lean_dec(v_j_7589_);
                        if v___x_7593_ == 0 {
                            lean_dec_ref(v_ys_7592_);
                            lean_dec_ref(v_ys_7590_);
                            lean_dec(v_x_7414_);
                            return v___x_7593_;
                        } else {
                            v___x_7594_ =
                                l_Lean_IR_args_alphaEqv(v_x_7414_, v_ys_7590_, v_ys_7592_);
                            lean_dec_ref(v_ys_7592_);
                            lean_dec_ref(v_ys_7590_);
                            lean_dec(v_x_7414_);
                            return v___x_7594_;
                        }
                    } else {
                        lean_dec_ref_known(v_x_7415_, 2);
                        lean_dec(v_x_7416_);
                        lean_dec(v_x_7414_);
                        v___x_7595_ = 0;
                        return v___x_7595_;
                    }
                }
                _ => {
                    lean_dec(v_x_7414_);
                    if lean_obj_tag(v_x_7416_) == 12 {
                        v___x_7596_ = 1;
                        return v___x_7596_;
                    } else {
                        lean_dec(v_x_7416_);
                        v___x_7597_ = 0;
                        return v___x_7597_;
                    }
                }
            },
            1 => {
                if v___y_7421_ == 0 {
                    if v___y_7418_ == 0 {
                        v_x_7414_ = v___y_7420_;
                        v_x_7415_ = v___y_7422_;
                        v_x_7416_ = v___y_7419_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___y_7422_);
                        lean_dec(v___y_7420_);
                        lean_dec(v___y_7419_);
                        return v___y_7421_;
                    }
                } else {
                    if v___y_7418_ == 0 {
                        lean_dec(v___y_7422_);
                        lean_dec(v___y_7420_);
                        lean_dec(v___y_7419_);
                        return v___y_7418_;
                    } else {
                        v_x_7414_ = v___y_7420_;
                        v_x_7415_ = v___y_7422_;
                        v_x_7416_ = v___y_7419_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_7433_ == 0 {
                    lean_dec(v___y_7432_);
                    lean_dec(v___y_7428_);
                    lean_dec(v___y_7427_);
                    return v___y_7433_;
                } else {
                    if v___y_7431_ == 0 {
                        if v___y_7430_ == 0 {
                            v___y_7418_ = v___y_7426_;
                            v___y_7419_ = v___y_7428_;
                            v___y_7420_ = v___y_7427_;
                            v___y_7421_ = v___y_7429_;
                            v___y_7422_ = v___y_7432_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___y_7432_);
                            lean_dec(v___y_7428_);
                            lean_dec(v___y_7427_);
                            return v___y_7431_;
                        }
                    } else {
                        if v___y_7430_ == 0 {
                            lean_dec(v___y_7432_);
                            lean_dec(v___y_7428_);
                            lean_dec(v___y_7427_);
                            return v___y_7430_;
                        } else {
                            v___y_7418_ = v___y_7426_;
                            v___y_7419_ = v___y_7428_;
                            v___y_7420_ = v___y_7427_;
                            v___y_7421_ = v___y_7429_;
                            v___y_7422_ = v___y_7432_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_7446_ =
                    l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7435_, v_x_u2081_7436_, v_x_u2082_7441_);
                lean_dec(v_x_u2082_7441_);
                lean_dec(v_x_u2081_7436_);
                if v___x_7446_ == 0 {
                    lean_dec(v_n_u2082_7442_);
                    lean_dec(v_n_u2081_7437_);
                    v___y_7426_ = v_p_u2082_7444_;
                    v___y_7427_ = v_00_u03c1_7435_;
                    v___y_7428_ = v_b_u2082_7445_;
                    v___y_7429_ = v_p_u2081_7439_;
                    v___y_7430_ = v_c_u2082_7443_;
                    v___y_7431_ = v_c_u2081_7438_;
                    v___y_7432_ = v_b_u2081_7440_;
                    v___y_7433_ = v___x_7446_;
                    state = 2;
                    continue;
                } else {
                    v___x_7447_ = lean_nat_dec_eq(v_n_u2081_7437_, v_n_u2082_7442_);
                    lean_dec(v_n_u2082_7442_);
                    lean_dec(v_n_u2081_7437_);
                    v___y_7426_ = v_p_u2082_7444_;
                    v___y_7427_ = v_00_u03c1_7435_;
                    v___y_7428_ = v_b_u2082_7445_;
                    v___y_7429_ = v_p_u2081_7439_;
                    v___y_7430_ = v_c_u2082_7443_;
                    v___y_7431_ = v_c_u2081_7438_;
                    v___y_7432_ = v_b_u2081_7440_;
                    v___y_7433_ = v___x_7447_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_7457_ == 0 {
                    lean_dec(v_b_7455_);
                    lean_dec(v_x_7452_);
                    lean_dec(v_b_7451_);
                    lean_dec(v_x_7448_);
                    lean_dec(v_x_7414_);
                    return v___y_7457_;
                } else {
                    v___x_7458_ = l_Lean_IR_addVarRename(v_x_7414_, v_x_7448_, v_x_7452_);
                    v_x_7414_ = v___x_7458_;
                    v_x_7415_ = v_b_7451_;
                    v_x_7416_ = v_b_7455_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                if v___y_7487_ == 0 {
                    lean_dec(v_b_7485_);
                    lean_dec(v_y_7484_);
                    lean_dec(v_b_7481_);
                    lean_dec(v_y_7480_);
                    lean_dec(v_x_7414_);
                    return v___y_7487_;
                } else {
                    v___x_7488_ = l_Lean_IR_Arg_alphaEqv(v_x_7414_, v_y_7480_, v_y_7484_);
                    lean_dec(v_y_7484_);
                    lean_dec(v_y_7480_);
                    if v___x_7488_ == 0 {
                        lean_dec(v_b_7485_);
                        lean_dec(v_b_7481_);
                        lean_dec(v_x_7414_);
                        return v___x_7488_;
                    } else {
                        v_x_7415_ = v_b_7481_;
                        v_x_7416_ = v_b_7485_;
                        state = 0;
                        continue;
                    }
                }
            }
            6 => {
                if v___y_7500_ == 0 {
                    lean_dec(v_b_7498_);
                    lean_dec(v_b_7495_);
                    lean_dec(v_x_7414_);
                    return v___y_7500_;
                } else {
                    v_x_7415_ = v_b_7495_;
                    v_x_7416_ = v_b_7498_;
                    state = 0;
                    continue;
                }
            }
            7 => {
                if v___y_7514_ == 0 {
                    lean_dec(v_b_7512_);
                    lean_dec(v_y_7511_);
                    lean_dec(v_b_7508_);
                    lean_dec(v_y_7507_);
                    lean_dec(v_x_7414_);
                    return v___y_7514_;
                } else {
                    v___x_7515_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_y_7507_, v_y_7511_);
                    lean_dec(v_y_7511_);
                    lean_dec(v_y_7507_);
                    if v___x_7515_ == 0 {
                        lean_dec(v_b_7512_);
                        lean_dec(v_b_7508_);
                        lean_dec(v_x_7414_);
                        return v___x_7515_;
                    } else {
                        v_x_7415_ = v_b_7508_;
                        v_x_7416_ = v_b_7512_;
                        state = 0;
                        continue;
                    }
                }
            }
            8 => {
                if v___y_7534_ == 0 {
                    lean_dec(v_b_7531_);
                    lean_dec(v_ty_7530_);
                    lean_dec(v_y_7529_);
                    lean_dec(v_b_7525_);
                    lean_dec(v_ty_7524_);
                    lean_dec(v_y_7523_);
                    lean_dec(v_x_7414_);
                    return v___y_7534_;
                } else {
                    if v___x_7532_ == 0 {
                        lean_dec(v_b_7531_);
                        lean_dec(v_ty_7530_);
                        lean_dec(v_y_7529_);
                        lean_dec(v_b_7525_);
                        lean_dec(v_ty_7524_);
                        lean_dec(v_y_7523_);
                        lean_dec(v_x_7414_);
                        return v___x_7532_;
                    } else {
                        v___x_7535_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_y_7523_, v_y_7529_);
                        lean_dec(v_y_7529_);
                        lean_dec(v_y_7523_);
                        if v___x_7535_ == 0 {
                            lean_dec(v_b_7531_);
                            lean_dec(v_ty_7530_);
                            lean_dec(v_b_7525_);
                            lean_dec(v_ty_7524_);
                            lean_dec(v_x_7414_);
                            return v___x_7535_;
                        } else {
                            v___x_7536_ = l_Lean_IR_instBEqIRType_beq(v_ty_7524_, v_ty_7530_);
                            lean_dec(v_ty_7530_);
                            lean_dec(v_ty_7524_);
                            if v___x_7536_ == 0 {
                                lean_dec(v_b_7531_);
                                lean_dec(v_b_7525_);
                                lean_dec(v_x_7414_);
                                return v___x_7536_;
                            } else {
                                v_x_7415_ = v_b_7525_;
                                v_x_7416_ = v_b_7531_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            9 => {
                if v___y_7577_ == 0 {
                    lean_dec_ref(v_cs_7575_);
                    lean_dec_ref(v_cs_7572_);
                    lean_dec(v_x_7414_);
                    return v___y_7577_;
                } else {
                    v___x_7578_ = lean_array_get_size(v_cs_7572_);
                    v___x_7579_ = lean_array_get_size(v_cs_7575_);
                    v___x_7580_ = lean_nat_dec_eq(v___x_7578_, v___x_7579_);
                    if v___x_7580_ == 0 {
                        lean_dec_ref(v_cs_7575_);
                        lean_dec_ref(v_cs_7572_);
                        lean_dec(v_x_7414_);
                        return v___x_7580_;
                    } else {
                        v___x_7581_ =
                            l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
                                v_x_7414_,
                                v_cs_7572_,
                                v_cs_7575_,
                                v___x_7578_,
                            );
                        lean_dec_ref(v_cs_7575_);
                        lean_dec_ref(v_cs_7572_);
                        return v___x_7581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
    mut v_x_7598_: *mut LeanObject,
    mut v_xs_7599_: *mut LeanObject,
    mut v_ys_7600_: *mut LeanObject,
    mut v_x_7601_: *mut LeanObject,
) -> u8 {
    let mut v_zero_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_7603_: u8 = 0;
    let mut v_one_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_7605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7607_: u8 = 0;
    let mut v___x_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_7611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_info_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: u8 = 0;
    let mut v___x_7616_: u8 = 0;
    let mut v_b_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7602_ = lean_unsigned_to_nat(0);
                v_isZero_7603_ = lean_nat_dec_eq(v_x_7601_, v_zero_7602_);
                if v_isZero_7603_ == 1 {
                    lean_dec(v_x_7601_);
                    lean_dec(v_x_7598_);
                    return v_isZero_7603_;
                } else {
                    v_one_7604_ = lean_unsigned_to_nat(1);
                    v_n_7605_ = lean_nat_sub(v_x_7601_, v_one_7604_);
                    lean_dec(v_x_7601_);
                    v___x_7609_ = lean_array_fget_borrowed(v_xs_7599_, v_n_7605_);
                    v___x_7610_ = lean_array_fget_borrowed(v_ys_7600_, v_n_7605_);
                    if lean_obj_tag(v___x_7609_) == 0 {
                        if lean_obj_tag(v___x_7610_) == 0 {
                            v_info_7611_ = lean_ctor_get(v___x_7609_, 0);
                            v_b_7612_ = lean_ctor_get(v___x_7609_, 1);
                            v_info_7613_ = lean_ctor_get(v___x_7610_, 0);
                            v_b_7614_ = lean_ctor_get(v___x_7610_, 1);
                            v___x_7615_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_7611_, v_info_7613_);
                            if v___x_7615_ == 0 {
                                v___y_7607_ = v___x_7615_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_b_7614_);
                                lean_inc(v_b_7612_);
                                lean_inc(v_x_7598_);
                                v___x_7616_ =
                                    l_Lean_IR_FnBody_alphaEqv(v_x_7598_, v_b_7612_, v_b_7614_);
                                v___y_7607_ = v___x_7616_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_n_7605_);
                            lean_dec(v_x_7598_);
                            return v_isZero_7603_;
                        }
                    } else {
                        if lean_obj_tag(v___x_7610_) == 1 {
                            v_b_7617_ = lean_ctor_get(v___x_7609_, 0);
                            v_b_7618_ = lean_ctor_get(v___x_7610_, 0);
                            lean_inc(v_b_7618_);
                            lean_inc(v_b_7617_);
                            lean_inc(v_x_7598_);
                            v___x_7619_ =
                                l_Lean_IR_FnBody_alphaEqv(v_x_7598_, v_b_7617_, v_b_7618_);
                            v___y_7607_ = v___x_7619_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_n_7605_);
                            lean_dec(v_x_7598_);
                            return v_isZero_7603_;
                        }
                    }
                }
            }
            1 => {
                if v___y_7607_ == 0 {
                    lean_dec(v_n_7605_);
                    lean_dec(v_x_7598_);
                    return v___y_7607_;
                } else {
                    v_x_7601_ = v_n_7605_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(
    mut v_x_7620_: *mut LeanObject,
    mut v_xs_7621_: *mut LeanObject,
    mut v_ys_7622_: *mut LeanObject,
    mut v_x_7623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7624_: u8 = 0;
    let mut v_r_7625_: *mut LeanObject = core::ptr::null_mut();
    v_res_7624_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
        v_x_7620_, v_xs_7621_, v_ys_7622_, v_x_7623_,
    );
    lean_dec_ref(v_ys_7622_);
    lean_dec_ref(v_xs_7621_);
    v_r_7625_ = lean_box((v_res_7624_) as usize);
    return v_r_7625_;
}
pub unsafe fn l_Lean_IR_FnBody_alphaEqv___boxed(
    mut v_x_7626_: *mut LeanObject,
    mut v_x_7627_: *mut LeanObject,
    mut v_x_7628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7629_: u8 = 0;
    let mut v_r_7630_: *mut LeanObject = core::ptr::null_mut();
    v_res_7629_ = l_Lean_IR_FnBody_alphaEqv(v_x_7626_, v_x_7627_, v_x_7628_);
    v_r_7630_ = lean_box((v_res_7629_) as usize);
    return v_r_7630_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(
    mut v_x_7631_: *mut LeanObject,
    mut v_xs_7632_: *mut LeanObject,
    mut v_ys_7633_: *mut LeanObject,
    mut v_hsz_7634_: *mut LeanObject,
    mut v_x_7635_: *mut LeanObject,
    mut v_x_7636_: *mut LeanObject,
) -> u8 {
    let mut v___x_7637_: u8 = 0;
    v___x_7637_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
        v_x_7631_, v_xs_7632_, v_ys_7633_, v_x_7635_,
    );
    return v___x_7637_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(
    mut v_x_7638_: *mut LeanObject,
    mut v_xs_7639_: *mut LeanObject,
    mut v_ys_7640_: *mut LeanObject,
    mut v_hsz_7641_: *mut LeanObject,
    mut v_x_7642_: *mut LeanObject,
    mut v_x_7643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7644_: u8 = 0;
    let mut v_r_7645_: *mut LeanObject = core::ptr::null_mut();
    v_res_7644_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(
        v_x_7638_,
        v_xs_7639_,
        v_ys_7640_,
        v_hsz_7641_,
        v_x_7642_,
        v_x_7643_,
    );
    lean_dec_ref(v_ys_7640_);
    lean_dec_ref(v_xs_7639_);
    v_r_7645_ = lean_box((v_res_7644_) as usize);
    return v_r_7645_;
}
pub unsafe fn l_Lean_IR_FnBody_beq(
    mut v_b_u2081_7646_: *mut LeanObject,
    mut v_b_u2082_7647_: *mut LeanObject,
) -> u8 {
    let mut v___x_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: u8 = 0;
    v___x_7648_ = lean_box(1);
    v___x_7649_ = l_Lean_IR_FnBody_alphaEqv(v___x_7648_, v_b_u2081_7646_, v_b_u2082_7647_);
    return v___x_7649_;
}
pub unsafe fn l_Lean_IR_FnBody_beq___boxed(
    mut v_b_u2081_7650_: *mut LeanObject,
    mut v_b_u2082_7651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7652_: u8 = 0;
    let mut v_r_7653_: *mut LeanObject = core::ptr::null_mut();
    v_res_7652_ = l_Lean_IR_FnBody_beq(v_b_u2081_7650_, v_b_u2082_7651_);
    v_r_7653_ = lean_box((v_res_7652_) as usize);
    return v_r_7653_;
}
pub unsafe fn l_Lean_IR_mkIf(
    mut v_x_7674_: *mut LeanObject,
    mut v_t_7675_: *mut LeanObject,
    mut v_e_7676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut LeanObject = core::ptr::null_mut();
    v___x_7677_ = l_Lean_IR_mkIf___closed__1;
    v___x_7678_ = lean_box(1);
    v___x_7679_ = l_Lean_IR_mkIf___closed__4;
    v___x_7680_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7680_, 0, v___x_7679_);
    lean_ctor_set(v___x_7680_, 1, v_e_7676_);
    v___x_7681_ = l_Lean_IR_mkIf___closed__7;
    v___x_7682_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_7682_, 0, v___x_7681_);
    lean_ctor_set(v___x_7682_, 1, v_t_7675_);
    v___x_7683_ = lean_unsigned_to_nat(2);
    v___x_7684_ = lean_mk_empty_array_with_capacity(v___x_7683_);
    v___x_7685_ = lean_array_push(v___x_7684_, v___x_7680_);
    v___x_7686_ = lean_array_push(v___x_7685_, v___x_7682_);
    v___x_7687_ = lean_alloc_ctor(9, 4, (0) as u32);
    lean_ctor_set(v___x_7687_, 0, v___x_7677_);
    lean_ctor_set(v___x_7687_, 1, v_x_7674_);
    lean_ctor_set(v___x_7687_, 2, v___x_7678_);
    lean_ctor_set(v___x_7687_, 3, v___x_7686_);
    return v___x_7687_;
}
pub unsafe fn l_Lean_IR_getUnboxOpName(mut v_t_7694_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_t_7694_) {
        5 => {
            let mut v___x_7695_: *mut LeanObject = core::ptr::null_mut();
            v___x_7695_ = l_Lean_IR_getUnboxOpName___closed__0;
            return v___x_7695_;
        }
        3 => {
            let mut v___x_7696_: *mut LeanObject = core::ptr::null_mut();
            v___x_7696_ = l_Lean_IR_getUnboxOpName___closed__1;
            return v___x_7696_;
        }
        4 => {
            let mut v___x_7697_: *mut LeanObject = core::ptr::null_mut();
            v___x_7697_ = l_Lean_IR_getUnboxOpName___closed__2;
            return v___x_7697_;
        }
        0 => {
            let mut v___x_7698_: *mut LeanObject = core::ptr::null_mut();
            v___x_7698_ = l_Lean_IR_getUnboxOpName___closed__3;
            return v___x_7698_;
        }
        9 => {
            let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
            v___x_7699_ = l_Lean_IR_getUnboxOpName___closed__4;
            return v___x_7699_;
        }
        _ => {
            let mut v___x_7700_: *mut LeanObject = core::ptr::null_mut();
            v___x_7700_ = l_Lean_IR_getUnboxOpName___closed__5;
            return v___x_7700_;
        }
    }
}
pub unsafe fn l_Lean_IR_getUnboxOpName___boxed(mut v_t_7701_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_7702_: *mut LeanObject = core::ptr::null_mut();
    v_res_7702_ = l_Lean_IR_getUnboxOpName(v_t_7701_);
    lean_dec(v_t_7701_);
    return v_res_7702_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_IR_instInhabitedVarId_default = _init_l_Lean_IR_instInhabitedVarId_default();
    lean_mark_persistent(l_Lean_IR_instInhabitedVarId_default);
    l_Lean_IR_instInhabitedVarId = _init_l_Lean_IR_instInhabitedVarId();
    lean_mark_persistent(l_Lean_IR_instInhabitedVarId);
    l_Lean_IR_instInhabitedJoinPointId_default = _init_l_Lean_IR_instInhabitedJoinPointId_default();
    lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId_default);
    l_Lean_IR_instInhabitedJoinPointId = _init_l_Lean_IR_instInhabitedJoinPointId();
    lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId);
    l_Lean_IR_instInhabitedIRType_default = _init_l_Lean_IR_instInhabitedIRType_default();
    lean_mark_persistent(l_Lean_IR_instInhabitedIRType_default);
    l_Lean_IR_instInhabitedIRType = _init_l_Lean_IR_instInhabitedIRType();
    lean_mark_persistent(l_Lean_IR_instInhabitedIRType);
    l_Lean_IR_FnBody_nil = _init_l_Lean_IR_FnBody_nil();
    lean_mark_persistent(l_Lean_IR_FnBody_nil);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_ExternAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Basic(builtin);
}
