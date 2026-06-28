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
pub static mut l_Lean_IR_instInhabitedVarId_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_IR_instInhabitedVarId: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_instBEqVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqVarId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqVarId___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instBEqVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqVarId___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instHashableVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instHashableVarId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instHashableVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instHashableVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__1_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__4_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__5_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__8_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__11_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId_repr___redArg___closed__12_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprVarId_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instReprVarId_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instReprVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instReprVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprVarId___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedJoinPointId_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_IR_instInhabitedJoinPointId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instBEqJoinPointId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqJoinPointId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqJoinPointId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instBEqJoinPointId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instHashableJoinPointId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instHashableJoinPointId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instHashableJoinPointId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instHashableJoinPointId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instHashableJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprJoinPointId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instReprJoinPointId_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instReprJoinPointId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instReprJoinPointId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringVarId___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instToStringVarId___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringVarId___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instToStringVarId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToStringVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringJoinPointId___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instToStringJoinPointId___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringJoinPointId___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instToStringJoinPointId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instToStringJoinPointId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instToStringJoinPointId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instToStringJoinPointId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instToStringJoinPointId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedIRType_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_IR_instInhabitedIRType: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_instBEqIRType___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqIRType_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqIRType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqIRType___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instBEqIRType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqIRType___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__2_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprIRType_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__2_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprIRType_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__4_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 105, 110, 116,
            49, 54, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__6_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 105, 110, 116,
            51, 50, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__8_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 117, 105, 110, 116,
            54, 52, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__10_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprIRType_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__12_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 101, 114, 97, 115,
            101, 100, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__13_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__12_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__14_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 111, 98, 106, 101, 99,
            116, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__15_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__16_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprIRType_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__18_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprIRType_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__19_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__18_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__20_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 116, 97, 103, 103,
            101, 100, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__21_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__20_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__22_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprIRType_repr___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__23_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__22_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprIRType_repr___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprIRType_repr___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_IR_instReprIRType_repr___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprIRType_repr___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprIRType_repr___closed__26_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 73, 82, 46, 73, 82, 84, 121, 112, 101, 46, 115, 116, 114, 117,
            99, 116, 0,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__27_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__26_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__28_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__27_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__1_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__4_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__29_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprIRType_repr___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__30_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__29_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType_repr___closed__31_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__30_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprIRType_repr___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType_repr___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprIRType___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instReprIRType_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instReprIRType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instReprIRType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprIRType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedArg_default___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_IR_instInhabitedArg_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedArg_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedArg_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedArg_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedArg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedArg_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instBEqArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqArg_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instBEqArg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__0_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprArg_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprArg_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__2_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprArg_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprArg_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprArg_repr___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instReprArg_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instReprArg_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instReprArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instReprArg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedLitVal_default___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_IR_instInhabitedLitVal_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedLitVal_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedLitVal_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedLitVal_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedLitVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedLitVal_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instBEqLitVal___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqLitVal_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqLitVal___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqLitVal___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instBEqLitVal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqLitVal___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
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
static mut l_Lean_IR_instInhabitedCtorInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedCtorInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedCtorInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instBEqCtorInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instBEqCtorInfo_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqCtorInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instBEqCtorInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprCtorInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instReprCtorInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instReprCtorInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instReprCtorInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprCtorInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedExpr_default___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_IR_instInhabitedExpr_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedExpr_default___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedExpr_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedExpr_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedExpr_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedParam_default___closed__0_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            0 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedParam_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedParam_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedParam_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedParam_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedParam: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedParam_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprParam_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instReprVarId_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprParam_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprParam_repr___redArg___closed__5_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprParam_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprParam_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprParam_repr___redArg___closed__8_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_instReprParam_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instReprParam_repr___redArg___closed__9_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instReprParam_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_instReprParam_repr___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_instReprParam_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instReprParam___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_instReprParam_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instReprParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instReprParam: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instReprParam___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_IR_instInhabitedFnBody_default__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 9,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instInhabitedFnBody_default__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedFnBody_default__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedFnBody: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedAlt_default__1___closed__0_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_IR_instInhabitedCtorInfo_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_IR_instInhabitedFnBody_default__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_IR_instInhabitedAlt_default__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedAlt_default__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedAlt_default__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedAlt_default__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedAlt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedAlt_default__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_FnBody_nil: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_IR_Alt_modifyBodyM___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_IR_Alt_modifyBodyM___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_IR_Alt_modifyBodyM___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Alt_modifyBodyM___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_FnBody_flatten___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_IR_FnBody_flatten___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_FnBody_flatten___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_reshapeAux___closed__0_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 65, 114, 114, 97, 121, 46, 66, 97, 115,
            105, 99, 0,
        ],
    };
static mut l_Lean_IR_reshapeAux___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_reshapeAux___closed__1_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_reshapeAux___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_reshapeAux___closed__2_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [105, 110, 100, 101, 120, 32, 0],
    };
static mut l_Lean_IR_reshapeAux___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_reshapeAux___closed__3_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_reshapeAux___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_reshapeAux___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_modifyJPs___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_modifyJPs___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_modifyJPs___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_modifyJPs___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_modifyJPs___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_modifyJPs___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_modifyJPs___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_modifyJPs___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_modifyJPs___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_modifyJPs___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_modifyJPs___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_modifyJPs___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedDecl_default___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_IR_instInhabitedDecl_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instInhabitedDecl_default___closed__1_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
                + 0) as u16,
            other: 4,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_instInhabitedDecl_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedDecl_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instInhabitedDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instInhabitedDecl_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Decl_updateBody_x21___closed__0_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_Decl_updateBody_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Decl_updateBody_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Decl_updateBody_x21___closed__1_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_Decl_updateBody_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Decl_updateBody_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_Decl_updateBody_x21___closed__2_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_Decl_updateBody_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_Decl_updateBody_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_IR_Decl_updateBody_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_IR_Decl_updateBody_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_IR_instAlphaEqvVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_VarId_alphaEqv___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instAlphaEqvVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instAlphaEqvVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instAlphaEqvArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_Arg_alphaEqv___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instAlphaEqvArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instAlphaEqvArg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instAlphaEqvArrayArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_args_alphaEqv___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instAlphaEqvArrayArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArrayArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instAlphaEqvArrayArg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvArrayArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instAlphaEqvExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_Expr_alphaEqv___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instAlphaEqvExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instAlphaEqvExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instAlphaEqvExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_instBEqFnBody___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_IR_FnBody_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_IR_instBEqFnBody___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqFnBody___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_IR_instBEqFnBody: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_instBEqFnBody___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_mkIf___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_mkIf___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_mkIf___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_mkIf___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_mkIf___closed__2_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_mkIf___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_IR_mkIf___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_IR_mkIf___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__2_value) as *mut crate::leanh::LeanObject,
            15761733860085307253 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_mkIf___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_mkIf___closed__4_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__3_value) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_mkIf___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_mkIf___closed__5_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_mkIf___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_IR_mkIf___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__0_value) as *mut crate::leanh::LeanObject,
            12882480457794858234 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_IR_mkIf___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__5_value) as *mut crate::leanh::LeanObject,
            9255189395584251158 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_mkIf___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_mkIf___closed__7_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_IR_mkIf___closed__6_value) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_IR_mkIf___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_mkIf___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_getUnboxOpName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__1_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_getUnboxOpName___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__2_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_getUnboxOpName___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__3_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_getUnboxOpName___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__4_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_getUnboxOpName___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_IR_getUnboxOpName___closed__5_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_IR_getUnboxOpName___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_IR_getUnboxOpName___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_IR_instInhabitedVarId_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3852_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_3852_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedVarId() -> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_3853_;
}
pub unsafe fn l_Lean_IR_instBEqVarId_beq(
    mut v_x_3854_: *mut crate::leanh::LeanObject,
    mut v_x_3855_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3856_: u8 = 0;
    v___x_3856_ = lean_nat_dec_eq(v_x_3854_, v_x_3855_);
    return v___x_3856_;
}
pub unsafe fn l_Lean_IR_instBEqVarId_beq___boxed(
    mut v_x_3857_: *mut crate::leanh::LeanObject,
    mut v_x_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3859_: u8 = 0;
    let mut v_r_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Lean_IR_instBEqVarId_beq(v_x_3857_, v_x_3858_);
    crate::leanh::lean_dec(v_x_3858_);
    crate::leanh::lean_dec(v_x_3857_);
    v_r_3860_ = crate::leanh::lean_box((v_res_3859_) as usize);
    return v_r_3860_;
}
pub unsafe fn l_Lean_IR_instHashableVarId_hash(
    mut v_x_3863_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_3864_: u64 = 0;
    let mut v___x_3865_: u64 = 0;
    let mut v___x_3866_: u64 = 0;
    v___x_3864_ = 0u64;
    v___x_3865_ = lean_uint64_of_nat(v_x_3863_);
    v___x_3866_ = lean_uint64_mix_hash(v___x_3864_, v___x_3865_);
    return v___x_3866_;
}
pub unsafe fn l_Lean_IR_instHashableVarId_hash___boxed(
    mut v_x_3867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3868_: u64 = 0;
    let mut v_r_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3868_ = l_Lean_IR_instHashableVarId_hash(v_x_3867_);
    crate::leanh::lean_dec(v_x_3867_);
    v_r_3869_ = crate::leanh::lean_box_uint64(v_res_3868_);
    return v_r_3869_;
}
pub unsafe fn l_Nat_cast___at___00Lean_IR_instReprVarId_repr_spec__0(
    mut v_a_3872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3873_ = lean_nat_to_int(v_a_3872_);
    return v___x_3873_;
}
pub unsafe fn _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3887_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_3888_ = lean_nat_to_int(v___x_3887_);
    return v___x_3888_;
}
pub unsafe fn _init_l_Lean_IR_instReprVarId_repr___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = l_Lean_IR_instReprVarId_repr___redArg___closed__0;
    v___x_3891_ = lean_string_length(v___x_3890_);
    return v___x_3891_;
}
pub unsafe fn _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3892_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__9_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__9,
    );
    v___x_3893_ = lean_nat_to_int(v___x_3892_);
    return v___x_3893_;
}
pub unsafe fn l_Lean_IR_instReprVarId_repr___redArg(
    mut v_x_3898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3899_ = l_Lean_IR_instReprVarId_repr___redArg___closed__6;
    v___x_3900_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7,
    );
    v___x_3901_ = l_Nat_reprFast(v_x_3898_);
    v___x_3902_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3902_, 0, v___x_3901_);
    v___x_3903_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3903_, 0, v___x_3900_);
    crate::leanh::lean_ctor_set(v___x_3903_, 1, v___x_3902_);
    v___x_3904_ = 0;
    v___x_3905_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3905_, 0, v___x_3903_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3905_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3904_,
    );
    v___x_3906_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3906_, 0, v___x_3899_);
    crate::leanh::lean_ctor_set(v___x_3906_, 1, v___x_3905_);
    v___x_3907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_3908_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_3909_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3909_, 0, v___x_3908_);
    crate::leanh::lean_ctor_set(v___x_3909_, 1, v___x_3906_);
    v___x_3910_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_3911_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3911_, 0, v___x_3909_);
    crate::leanh::lean_ctor_set(v___x_3911_, 1, v___x_3910_);
    v___x_3912_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3912_, 0, v___x_3907_);
    crate::leanh::lean_ctor_set(v___x_3912_, 1, v___x_3911_);
    v___x_3913_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3913_, 0, v___x_3912_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3913_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3904_,
    );
    return v___x_3913_;
}
pub unsafe fn l_Lean_IR_instReprVarId_repr(
    mut v_x_3914_: *mut crate::leanh::LeanObject,
    mut v_prec_3915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3916_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_3914_);
    return v___x_3916_;
}
pub unsafe fn l_Lean_IR_instReprVarId_repr___boxed(
    mut v_x_3917_: *mut crate::leanh::LeanObject,
    mut v_prec_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Lean_IR_instReprVarId_repr(v_x_3917_, v_prec_3918_);
    crate::leanh::lean_dec(v_prec_3918_);
    return v_res_3919_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedJoinPointId_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3922_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_3922_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedJoinPointId() -> *mut crate::leanh::LeanObject {
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3923_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_3923_;
}
pub unsafe fn l_Lean_IR_instBEqJoinPointId_beq(
    mut v_x_3924_: *mut crate::leanh::LeanObject,
    mut v_x_3925_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3926_: u8 = 0;
    v___x_3926_ = lean_nat_dec_eq(v_x_3924_, v_x_3925_);
    return v___x_3926_;
}
pub unsafe fn l_Lean_IR_instBEqJoinPointId_beq___boxed(
    mut v_x_3927_: *mut crate::leanh::LeanObject,
    mut v_x_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3929_: u8 = 0;
    let mut v_r_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3929_ = l_Lean_IR_instBEqJoinPointId_beq(v_x_3927_, v_x_3928_);
    crate::leanh::lean_dec(v_x_3928_);
    crate::leanh::lean_dec(v_x_3927_);
    v_r_3930_ = crate::leanh::lean_box((v_res_3929_) as usize);
    return v_r_3930_;
}
pub unsafe fn l_Lean_IR_instHashableJoinPointId_hash(
    mut v_x_3933_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_3934_: u64 = 0;
    let mut v___x_3935_: u64 = 0;
    let mut v___x_3936_: u64 = 0;
    v___x_3934_ = 0u64;
    v___x_3935_ = lean_uint64_of_nat(v_x_3933_);
    v___x_3936_ = lean_uint64_mix_hash(v___x_3934_, v___x_3935_);
    return v___x_3936_;
}
pub unsafe fn l_Lean_IR_instHashableJoinPointId_hash___boxed(
    mut v_x_3937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3938_: u64 = 0;
    let mut v_r_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3938_ = l_Lean_IR_instHashableJoinPointId_hash(v_x_3937_);
    crate::leanh::lean_dec(v_x_3937_);
    v_r_3939_ = crate::leanh::lean_box_uint64(v_res_3938_);
    return v_r_3939_;
}
pub unsafe fn l_Lean_IR_instReprJoinPointId_repr___redArg(
    mut v_x_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: u8 = 0;
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_IR_instReprVarId_repr___redArg___closed__6;
    v___x_3944_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__7_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__7,
    );
    v___x_3945_ = l_Nat_reprFast(v_x_3942_);
    v___x_3946_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3946_, 0, v___x_3945_);
    v___x_3947_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3947_, 0, v___x_3944_);
    crate::leanh::lean_ctor_set(v___x_3947_, 1, v___x_3946_);
    v___x_3948_ = 0;
    v___x_3949_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3949_, 0, v___x_3947_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3949_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3948_,
    );
    v___x_3950_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3943_);
    crate::leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
    v___x_3951_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_3952_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_3953_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3953_, 0, v___x_3952_);
    crate::leanh::lean_ctor_set(v___x_3953_, 1, v___x_3950_);
    v___x_3954_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_3955_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3955_, 0, v___x_3953_);
    crate::leanh::lean_ctor_set(v___x_3955_, 1, v___x_3954_);
    v___x_3956_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3956_, 0, v___x_3951_);
    crate::leanh::lean_ctor_set(v___x_3956_, 1, v___x_3955_);
    v___x_3957_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_3957_, 0, v___x_3956_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3957_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3948_,
    );
    return v___x_3957_;
}
pub unsafe fn l_Lean_IR_instReprJoinPointId_repr(
    mut v_x_3958_: *mut crate::leanh::LeanObject,
    mut v_prec_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_IR_instReprJoinPointId_repr___redArg(v_x_3958_);
    return v___x_3960_;
}
pub unsafe fn l_Lean_IR_instReprJoinPointId_repr___boxed(
    mut v_x_3961_: *mut crate::leanh::LeanObject,
    mut v_prec_3962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3963_ = l_Lean_IR_instReprJoinPointId_repr(v_x_3961_, v_prec_3962_);
    crate::leanh::lean_dec(v_prec_3962_);
    return v_res_3963_;
}
pub unsafe fn l_Lean_IR_Index_lt(
    mut v_a_3966_: *mut crate::leanh::LeanObject,
    mut v_b_3967_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3968_: u8 = 0;
    v___x_3968_ = lean_nat_dec_lt(v_a_3966_, v_b_3967_);
    return v___x_3968_;
}
pub unsafe fn l_Lean_IR_Index_lt___boxed(
    mut v_a_3969_: *mut crate::leanh::LeanObject,
    mut v_b_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3971_: u8 = 0;
    let mut v_r_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3971_ = l_Lean_IR_Index_lt(v_a_3969_, v_b_3970_);
    crate::leanh::lean_dec(v_b_3970_);
    crate::leanh::lean_dec(v_a_3969_);
    v_r_3972_ = crate::leanh::lean_box((v_res_3971_) as usize);
    return v_r_3972_;
}
pub unsafe fn l_Lean_IR_instToStringVarId___lam__0(
    mut v_a_3974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3975_ = l_Lean_IR_instToStringVarId___lam__0___closed__0;
    v___x_3976_ = l_Nat_reprFast(v_a_3974_);
    v___x_3977_ = lean_string_append(v___x_3975_, v___x_3976_);
    crate::leanh::lean_dec_ref(v___x_3976_);
    return v___x_3977_;
}
pub unsafe fn l_Lean_IR_instToStringJoinPointId___lam__0(
    mut v_a_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3982_ = l_Lean_IR_instToStringJoinPointId___lam__0___closed__0;
    v___x_3983_ = l_Nat_reprFast(v_a_3981_);
    v___x_3984_ = lean_string_append(v___x_3982_, v___x_3983_);
    crate::leanh::lean_dec_ref(v___x_3983_);
    return v___x_3984_;
}
pub unsafe fn l_Lean_IR_IRType_ctorIdx(
    mut v_x_3987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3987_) {
        0 => {
            let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3988_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3988_;
        }
        1 => {
            let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3989_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3989_;
        }
        2 => {
            let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3990_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3990_;
        }
        3 => {
            let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3991_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_3991_;
        }
        4 => {
            let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3992_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_3992_;
        }
        5 => {
            let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3993_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_3993_;
        }
        6 => {
            let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3994_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_3994_;
        }
        7 => {
            let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3995_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_3995_;
        }
        8 => {
            let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3996_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_3996_;
        }
        9 => {
            let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3997_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_3997_;
        }
        10 => {
            let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3998_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_3998_;
        }
        11 => {
            let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3999_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_3999_;
        }
        12 => {
            let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4000_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_4000_;
        }
        _ => {
            let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4001_ = crate::leanh::lean_unsigned_to_nat(13);
            return v___x_4001_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_ctorIdx___boxed(
    mut v_x_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4003_ = l_Lean_IR_IRType_ctorIdx(v_x_4002_);
    crate::leanh::lean_dec(v_x_4002_);
    return v_res_4003_;
}
pub unsafe fn l_Lean_IR_IRType_ctorElim___redArg(
    mut v_t_4004_: *mut crate::leanh::LeanObject,
    mut v_k_4005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_4004_) {
        10 => {
            let mut v_leanTypeName_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_types_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_leanTypeName_4006_ = crate::leanh::lean_ctor_get(v_t_4004_, 0);
            crate::leanh::lean_inc(v_leanTypeName_4006_);
            v_types_4007_ = crate::leanh::lean_ctor_get(v_t_4004_, 1);
            crate::leanh::lean_inc_ref(v_types_4007_);
            crate::leanh::lean_dec_ref_known(v_t_4004_, 2);
            v___x_4008_ =
                crate::leanh::lean_apply_2(v_k_4005_, v_leanTypeName_4006_, v_types_4007_);
            return v___x_4008_;
        }
        11 => {
            let mut v_leanTypeName_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_types_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_leanTypeName_4009_ = crate::leanh::lean_ctor_get(v_t_4004_, 0);
            crate::leanh::lean_inc(v_leanTypeName_4009_);
            v_types_4010_ = crate::leanh::lean_ctor_get(v_t_4004_, 1);
            crate::leanh::lean_inc_ref(v_types_4010_);
            crate::leanh::lean_dec_ref_known(v_t_4004_, 2);
            v___x_4011_ =
                crate::leanh::lean_apply_2(v_k_4005_, v_leanTypeName_4009_, v_types_4010_);
            return v___x_4011_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_4004_);
            return v_k_4005_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_ctorElim(
    mut v_motive__1_4012_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4013_: *mut crate::leanh::LeanObject,
    mut v_t_4014_: *mut crate::leanh::LeanObject,
    mut v_h_4015_: *mut crate::leanh::LeanObject,
    mut v_k_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4017_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4014_, v_k_4016_);
    return v___x_4017_;
}
pub unsafe fn l_Lean_IR_IRType_ctorElim___boxed(
    mut v_motive__1_4018_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4019_: *mut crate::leanh::LeanObject,
    mut v_t_4020_: *mut crate::leanh::LeanObject,
    mut v_h_4021_: *mut crate::leanh::LeanObject,
    mut v_k_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_IR_IRType_ctorElim(
        v_motive__1_4018_,
        v_ctorIdx_4019_,
        v_t_4020_,
        v_h_4021_,
        v_k_4022_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4019_);
    return v_res_4023_;
}
pub unsafe fn l_Lean_IR_IRType_float_elim___redArg(
    mut v_t_4024_: *mut crate::leanh::LeanObject,
    mut v_float_4025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4026_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4024_, v_float_4025_);
    return v___x_4026_;
}
pub unsafe fn l_Lean_IR_IRType_float_elim(
    mut v_motive__1_4027_: *mut crate::leanh::LeanObject,
    mut v_t_4028_: *mut crate::leanh::LeanObject,
    mut v_h_4029_: *mut crate::leanh::LeanObject,
    mut v_float_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4031_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4028_, v_float_4030_);
    return v___x_4031_;
}
pub unsafe fn l_Lean_IR_IRType_uint8_elim___redArg(
    mut v_t_4032_: *mut crate::leanh::LeanObject,
    mut v_uint8_4033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4034_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4032_, v_uint8_4033_);
    return v___x_4034_;
}
pub unsafe fn l_Lean_IR_IRType_uint8_elim(
    mut v_motive__1_4035_: *mut crate::leanh::LeanObject,
    mut v_t_4036_: *mut crate::leanh::LeanObject,
    mut v_h_4037_: *mut crate::leanh::LeanObject,
    mut v_uint8_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4039_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4036_, v_uint8_4038_);
    return v___x_4039_;
}
pub unsafe fn l_Lean_IR_IRType_uint16_elim___redArg(
    mut v_t_4040_: *mut crate::leanh::LeanObject,
    mut v_uint16_4041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4042_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4040_, v_uint16_4041_);
    return v___x_4042_;
}
pub unsafe fn l_Lean_IR_IRType_uint16_elim(
    mut v_motive__1_4043_: *mut crate::leanh::LeanObject,
    mut v_t_4044_: *mut crate::leanh::LeanObject,
    mut v_h_4045_: *mut crate::leanh::LeanObject,
    mut v_uint16_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4047_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4044_, v_uint16_4046_);
    return v___x_4047_;
}
pub unsafe fn l_Lean_IR_IRType_uint32_elim___redArg(
    mut v_t_4048_: *mut crate::leanh::LeanObject,
    mut v_uint32_4049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4048_, v_uint32_4049_);
    return v___x_4050_;
}
pub unsafe fn l_Lean_IR_IRType_uint32_elim(
    mut v_motive__1_4051_: *mut crate::leanh::LeanObject,
    mut v_t_4052_: *mut crate::leanh::LeanObject,
    mut v_h_4053_: *mut crate::leanh::LeanObject,
    mut v_uint32_4054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4055_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4052_, v_uint32_4054_);
    return v___x_4055_;
}
pub unsafe fn l_Lean_IR_IRType_uint64_elim___redArg(
    mut v_t_4056_: *mut crate::leanh::LeanObject,
    mut v_uint64_4057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4058_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4056_, v_uint64_4057_);
    return v___x_4058_;
}
pub unsafe fn l_Lean_IR_IRType_uint64_elim(
    mut v_motive__1_4059_: *mut crate::leanh::LeanObject,
    mut v_t_4060_: *mut crate::leanh::LeanObject,
    mut v_h_4061_: *mut crate::leanh::LeanObject,
    mut v_uint64_4062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4060_, v_uint64_4062_);
    return v___x_4063_;
}
pub unsafe fn l_Lean_IR_IRType_usize_elim___redArg(
    mut v_t_4064_: *mut crate::leanh::LeanObject,
    mut v_usize_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4064_, v_usize_4065_);
    return v___x_4066_;
}
pub unsafe fn l_Lean_IR_IRType_usize_elim(
    mut v_motive__1_4067_: *mut crate::leanh::LeanObject,
    mut v_t_4068_: *mut crate::leanh::LeanObject,
    mut v_h_4069_: *mut crate::leanh::LeanObject,
    mut v_usize_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4071_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4068_, v_usize_4070_);
    return v___x_4071_;
}
pub unsafe fn l_Lean_IR_IRType_erased_elim___redArg(
    mut v_t_4072_: *mut crate::leanh::LeanObject,
    mut v_erased_4073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4074_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4072_, v_erased_4073_);
    return v___x_4074_;
}
pub unsafe fn l_Lean_IR_IRType_erased_elim(
    mut v_motive__1_4075_: *mut crate::leanh::LeanObject,
    mut v_t_4076_: *mut crate::leanh::LeanObject,
    mut v_h_4077_: *mut crate::leanh::LeanObject,
    mut v_erased_4078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4079_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4076_, v_erased_4078_);
    return v___x_4079_;
}
pub unsafe fn l_Lean_IR_IRType_object_elim___redArg(
    mut v_t_4080_: *mut crate::leanh::LeanObject,
    mut v_object_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4082_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4080_, v_object_4081_);
    return v___x_4082_;
}
pub unsafe fn l_Lean_IR_IRType_object_elim(
    mut v_motive__1_4083_: *mut crate::leanh::LeanObject,
    mut v_t_4084_: *mut crate::leanh::LeanObject,
    mut v_h_4085_: *mut crate::leanh::LeanObject,
    mut v_object_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4087_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4084_, v_object_4086_);
    return v___x_4087_;
}
pub unsafe fn l_Lean_IR_IRType_tobject_elim___redArg(
    mut v_t_4088_: *mut crate::leanh::LeanObject,
    mut v_tobject_4089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4090_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4088_, v_tobject_4089_);
    return v___x_4090_;
}
pub unsafe fn l_Lean_IR_IRType_tobject_elim(
    mut v_motive__1_4091_: *mut crate::leanh::LeanObject,
    mut v_t_4092_: *mut crate::leanh::LeanObject,
    mut v_h_4093_: *mut crate::leanh::LeanObject,
    mut v_tobject_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4092_, v_tobject_4094_);
    return v___x_4095_;
}
pub unsafe fn l_Lean_IR_IRType_float32_elim___redArg(
    mut v_t_4096_: *mut crate::leanh::LeanObject,
    mut v_float32_4097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4096_, v_float32_4097_);
    return v___x_4098_;
}
pub unsafe fn l_Lean_IR_IRType_float32_elim(
    mut v_motive__1_4099_: *mut crate::leanh::LeanObject,
    mut v_t_4100_: *mut crate::leanh::LeanObject,
    mut v_h_4101_: *mut crate::leanh::LeanObject,
    mut v_float32_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4103_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4100_, v_float32_4102_);
    return v___x_4103_;
}
pub unsafe fn l_Lean_IR_IRType_struct_elim___redArg(
    mut v_t_4104_: *mut crate::leanh::LeanObject,
    mut v_struct_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4106_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4104_, v_struct_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Lean_IR_IRType_struct_elim(
    mut v_motive__1_4107_: *mut crate::leanh::LeanObject,
    mut v_t_4108_: *mut crate::leanh::LeanObject,
    mut v_h_4109_: *mut crate::leanh::LeanObject,
    mut v_struct_4110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4111_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4108_, v_struct_4110_);
    return v___x_4111_;
}
pub unsafe fn l_Lean_IR_IRType_union_elim___redArg(
    mut v_t_4112_: *mut crate::leanh::LeanObject,
    mut v_union_4113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4112_, v_union_4113_);
    return v___x_4114_;
}
pub unsafe fn l_Lean_IR_IRType_union_elim(
    mut v_motive__1_4115_: *mut crate::leanh::LeanObject,
    mut v_t_4116_: *mut crate::leanh::LeanObject,
    mut v_h_4117_: *mut crate::leanh::LeanObject,
    mut v_union_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4116_, v_union_4118_);
    return v___x_4119_;
}
pub unsafe fn l_Lean_IR_IRType_tagged_elim___redArg(
    mut v_t_4120_: *mut crate::leanh::LeanObject,
    mut v_tagged_4121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4120_, v_tagged_4121_);
    return v___x_4122_;
}
pub unsafe fn l_Lean_IR_IRType_tagged_elim(
    mut v_motive__1_4123_: *mut crate::leanh::LeanObject,
    mut v_t_4124_: *mut crate::leanh::LeanObject,
    mut v_h_4125_: *mut crate::leanh::LeanObject,
    mut v_tagged_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4124_, v_tagged_4126_);
    return v___x_4127_;
}
pub unsafe fn l_Lean_IR_IRType_void_elim___redArg(
    mut v_t_4128_: *mut crate::leanh::LeanObject,
    mut v_void_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4130_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4128_, v_void_4129_);
    return v___x_4130_;
}
pub unsafe fn l_Lean_IR_IRType_void_elim(
    mut v_motive__1_4131_: *mut crate::leanh::LeanObject,
    mut v_t_4132_: *mut crate::leanh::LeanObject,
    mut v_h_4133_: *mut crate::leanh::LeanObject,
    mut v_void_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4135_ = l_Lean_IR_IRType_ctorElim___redArg(v_t_4132_, v_void_4134_);
    return v___x_4135_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedIRType_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4136_ = crate::leanh::lean_box(0);
    return v___x_4136_;
}
pub unsafe fn _init_l_Lean_IR_instInhabitedIRType() -> *mut crate::leanh::LeanObject {
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = crate::leanh::lean_box(0);
    return v___x_4137_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(
    mut v_x_4138_: *mut crate::leanh::LeanObject,
    mut v_x_4139_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4138_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4139_) == 0 {
            let mut v___x_4140_: u8 = 0;
            v___x_4140_ = 1;
            return v___x_4140_;
        } else {
            let mut v___x_4141_: u8 = 0;
            v___x_4141_ = 0;
            return v___x_4141_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4139_) == 0 {
            let mut v___x_4142_: u8 = 0;
            v___x_4142_ = 0;
            return v___x_4142_;
        } else {
            let mut v_val_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4145_: u8 = 0;
            v_val_4143_ = crate::leanh::lean_ctor_get(v_x_4138_, 0);
            v_val_4144_ = crate::leanh::lean_ctor_get(v_x_4139_, 0);
            v___x_4145_ = lean_name_eq(v_val_4143_, v_val_4144_);
            return v___x_4145_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0___boxed(
    mut v_x_4146_: *mut crate::leanh::LeanObject,
    mut v_x_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4148_: u8 = 0;
    let mut v_r_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ =
        l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(v_x_4146_, v_x_4147_);
    crate::leanh::lean_dec(v_x_4147_);
    crate::leanh::lean_dec(v_x_4146_);
    v_r_4149_ = crate::leanh::lean_box((v_res_4148_) as usize);
    return v_r_4149_;
}
pub unsafe fn l_Lean_IR_instBEqIRType_beq(
    mut v_x_4150_: *mut crate::leanh::LeanObject,
    mut v_x_4151_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    v___x_4152_ = l_Lean_IR_IRType_ctorIdx(v_x_4150_);
    v___x_4153_ = l_Lean_IR_IRType_ctorIdx(v_x_4151_);
    v___x_4154_ = lean_nat_dec_eq(v___x_4152_, v___x_4153_);
    crate::leanh::lean_dec(v___x_4153_);
    crate::leanh::lean_dec(v___x_4152_);
    if v___x_4154_ == 0 {
        return v___x_4154_;
    } else {
        match crate::leanh::lean_obj_tag(v_x_4150_) {
            10 => {
                let mut v_leanTypeName_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_types_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_leanTypeName_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_types_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4159_: u8 = 0;
                v_leanTypeName_4155_ = crate::leanh::lean_ctor_get(v_x_4150_, 0);
                v_types_4156_ = crate::leanh::lean_ctor_get(v_x_4150_, 1);
                v_leanTypeName_4157_ = crate::leanh::lean_ctor_get(v_x_4151_, 0);
                v_types_4158_ = crate::leanh::lean_ctor_get(v_x_4151_, 1);
                v___x_4159_ = l_Option_instBEq_beq___at___00Lean_IR_instBEqIRType_beq_spec__0(
                    v_leanTypeName_4155_,
                    v_leanTypeName_4157_,
                );
                if v___x_4159_ == 0 {
                    return v___x_4159_;
                } else {
                    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                let mut v_leanTypeName_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_types_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_leanTypeName_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_types_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4168_: u8 = 0;
                v_leanTypeName_4164_ = crate::leanh::lean_ctor_get(v_x_4150_, 0);
                v_types_4165_ = crate::leanh::lean_ctor_get(v_x_4150_, 1);
                v_leanTypeName_4166_ = crate::leanh::lean_ctor_get(v_x_4151_, 0);
                v_types_4167_ = crate::leanh::lean_ctor_get(v_x_4151_, 1);
                v___x_4168_ = lean_name_eq(v_leanTypeName_4164_, v_leanTypeName_4166_);
                if v___x_4168_ == 0 {
                    return v___x_4168_;
                } else {
                    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_xs_4173_: *mut crate::leanh::LeanObject,
    mut v_ys_4174_: *mut crate::leanh::LeanObject,
    mut v_x_4175_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4177_: u8 = 0;
    let mut v_one_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4176_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4177_ = lean_nat_dec_eq(v_x_4175_, v_zero_4176_);
                if v_isZero_4177_ == 1 {
                    crate::leanh::lean_dec(v_x_4175_);
                    return v_isZero_4177_;
                } else {
                    v_one_4178_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4179_ = lean_nat_sub(v_x_4175_, v_one_4178_);
                    crate::leanh::lean_dec(v_x_4175_);
                    v___x_4180_ = lean_array_fget_borrowed(v_xs_4173_, v_n_4179_);
                    v___x_4181_ = lean_array_fget_borrowed(v_ys_4174_, v_n_4179_);
                    v___x_4182_ = l_Lean_IR_instBEqIRType_beq(v___x_4180_, v___x_4181_);
                    if v___x_4182_ == 0 {
                        crate::leanh::lean_dec(v_n_4179_);
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
    mut v_xs_4184_: *mut crate::leanh::LeanObject,
    mut v_ys_4185_: *mut crate::leanh::LeanObject,
    mut v_x_4186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4187_: u8 = 0;
    let mut v_r_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4187_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(
        v_xs_4184_, v_ys_4185_, v_x_4186_,
    );
    crate::leanh::lean_dec_ref(v_ys_4185_);
    crate::leanh::lean_dec_ref(v_xs_4184_);
    v_r_4188_ = crate::leanh::lean_box((v_res_4187_) as usize);
    return v_r_4188_;
}
pub unsafe fn l_Lean_IR_instBEqIRType_beq___boxed(
    mut v_x_4189_: *mut crate::leanh::LeanObject,
    mut v_x_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4191_: u8 = 0;
    let mut v_r_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4191_ = l_Lean_IR_instBEqIRType_beq(v_x_4189_, v_x_4190_);
    crate::leanh::lean_dec(v_x_4190_);
    crate::leanh::lean_dec(v_x_4189_);
    v_r_4192_ = crate::leanh::lean_box((v_res_4191_) as usize);
    return v_r_4192_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(
    mut v_xs_4193_: *mut crate::leanh::LeanObject,
    mut v_ys_4194_: *mut crate::leanh::LeanObject,
    mut v_hsz_4195_: *mut crate::leanh::LeanObject,
    mut v_x_4196_: *mut crate::leanh::LeanObject,
    mut v_x_4197_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4198_: u8 = 0;
    v___x_4198_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___redArg(
        v_xs_4193_, v_ys_4194_, v_x_4196_,
    );
    return v___x_4198_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1___boxed(
    mut v_xs_4199_: *mut crate::leanh::LeanObject,
    mut v_ys_4200_: *mut crate::leanh::LeanObject,
    mut v_hsz_4201_: *mut crate::leanh::LeanObject,
    mut v_x_4202_: *mut crate::leanh::LeanObject,
    mut v_x_4203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4204_: u8 = 0;
    let mut v_r_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4204_ = l_Array_isEqvAux___at___00Lean_IR_instBEqIRType_beq_spec__1(
        v_xs_4199_,
        v_ys_4200_,
        v_hsz_4201_,
        v_x_4202_,
        v_x_4203_,
    );
    crate::leanh::lean_dec_ref(v_ys_4200_);
    crate::leanh::lean_dec_ref(v_xs_4199_);
    v_r_4205_ = crate::leanh::lean_box((v_res_4204_) as usize);
    return v_r_4205_;
}
pub unsafe fn l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(
    mut v_x_4214_: *mut crate::leanh::LeanObject,
    mut v_x_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4214_) == 0 {
        let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4216_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__1;
        return v___x_4216_;
    } else {
        let mut v_val_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4217_ = crate::leanh::lean_ctor_get(v_x_4214_, 0);
        crate::leanh::lean_inc(v_val_4217_);
        crate::leanh::lean_dec_ref_known(v_x_4214_, 1);
        v___x_4218_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___closed__3;
        v___x_4219_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_4220_ = l_Lean_Name_reprPrec(v_val_4217_, v___x_4219_);
        v___x_4221_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4221_, 0, v___x_4218_);
        crate::leanh::lean_ctor_set(v___x_4221_, 1, v___x_4220_);
        v___x_4222_ = l_Repr_addAppParen(v___x_4221_, v_x_4215_);
        return v___x_4222_;
    }
}
pub unsafe fn l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0___boxed(
    mut v_x_4223_: *mut crate::leanh::LeanObject,
    mut v_x_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(v_x_4223_, v_x_4224_);
    crate::leanh::lean_dec(v_x_4224_);
    return v_res_4225_;
}
pub unsafe fn _init_l_Lean_IR_instReprIRType_repr___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4263_ = lean_nat_to_int(v___x_4262_);
    return v___x_4263_;
}
pub unsafe fn _init_l_Lean_IR_instReprIRType_repr___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4264_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_4265_ = lean_nat_to_int(v___x_4264_);
    return v___x_4265_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(
    mut v_x_4278_: *mut crate::leanh::LeanObject,
    mut v_x_4279_: *mut crate::leanh::LeanObject,
    mut v_x_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4285_: u8 = 0;
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4293_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4280_) == 0 {
                    crate::leanh::lean_dec(v_x_4278_);
                    return v_x_4279_;
                } else {
                    v_head_4281_ = crate::leanh::lean_ctor_get(v_x_4280_, 0);
                    v_tail_4282_ = crate::leanh::lean_ctor_get(v_x_4280_, 1);
                    v_isSharedCheck_4293_ = (!crate::leanh::lean_is_exclusive(v_x_4280_)) as u8;
                    if v_isSharedCheck_4293_ == 0 {
                        v___x_4284_ = v_x_4280_;
                        v_isShared_4285_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4282_);
                        crate::leanh::lean_inc(v_head_4281_);
                        crate::leanh::lean_dec(v_x_4280_);
                        v___x_4284_ = crate::leanh::lean_box(0);
                        v_isShared_4285_ = v_isSharedCheck_4293_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_4278_);
                if v_isShared_4285_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4284_, 5);
                    crate::leanh::lean_ctor_set(v___x_4284_, 1, v_x_4278_);
                    crate::leanh::lean_ctor_set(v___x_4284_, 0, v_x_4279_);
                    v___x_4287_ = v___x_4284_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4292_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_x_4279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4292_, 1, v_x_4278_);
                    v___x_4287_ = v_reuseFailAlloc_4292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4288_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4289_ = l_Lean_IR_instReprIRType_repr(v_head_4281_, v___x_4288_);
                v___x_4290_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4290_, 0, v___x_4287_);
                crate::leanh::lean_ctor_set(v___x_4290_, 1, v___x_4289_);
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
    mut v_x_4294_: *mut crate::leanh::LeanObject,
    mut v_x_4295_: *mut crate::leanh::LeanObject,
    mut v_x_4296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4296_) == 0 {
                    crate::leanh::lean_dec(v_x_4294_);
                    return v_x_4295_;
                } else {
                    v_head_4297_ = crate::leanh::lean_ctor_get(v_x_4296_, 0);
                    v_tail_4298_ = crate::leanh::lean_ctor_get(v_x_4296_, 1);
                    v_isSharedCheck_4309_ = (!crate::leanh::lean_is_exclusive(v_x_4296_)) as u8;
                    if v_isSharedCheck_4309_ == 0 {
                        v___x_4300_ = v_x_4296_;
                        v_isShared_4301_ = v_isSharedCheck_4309_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4298_);
                        crate::leanh::lean_inc(v_head_4297_);
                        crate::leanh::lean_dec(v_x_4296_);
                        v___x_4300_ = crate::leanh::lean_box(0);
                        v_isShared_4301_ = v_isSharedCheck_4309_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_x_4294_);
                if v_isShared_4301_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4300_, 5);
                    crate::leanh::lean_ctor_set(v___x_4300_, 1, v_x_4294_);
                    crate::leanh::lean_ctor_set(v___x_4300_, 0, v_x_4295_);
                    v___x_4303_ = v___x_4300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_x_4295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 1, v_x_4294_);
                    v___x_4303_ = v_reuseFailAlloc_4308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4304_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4305_ = l_Lean_IR_instReprIRType_repr(v_head_4297_, v___x_4304_);
                v___x_4306_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4306_, 0, v___x_4303_);
                crate::leanh::lean_ctor_set(v___x_4306_, 1, v___x_4305_);
                v___x_4307_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2_spec__3(v_x_4294_, v___x_4306_, v_tail_4298_);
                return v___x_4307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(
    mut v_x_4310_: *mut crate::leanh::LeanObject,
    mut v_x_4311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4310_) == 0 {
        let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4311_);
        v___x_4312_ = crate::leanh::lean_box(0);
        return v___x_4312_;
    } else {
        let mut v_tail_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_4313_ = crate::leanh::lean_ctor_get(v_x_4310_, 1);
        if crate::leanh::lean_obj_tag(v_tail_4313_) == 0 {
            let mut v_head_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_4311_);
            v_head_4314_ = crate::leanh::lean_ctor_get(v_x_4310_, 0);
            crate::leanh::lean_inc(v_head_4314_);
            crate::leanh::lean_dec_ref_known(v_x_4310_, 2);
            v___x_4315_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_4314_);
            return v___x_4315_;
        } else {
            let mut v_head_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_4313_);
            v_head_4316_ = crate::leanh::lean_ctor_get(v_x_4310_, 0);
            crate::leanh::lean_inc(v_head_4316_);
            crate::leanh::lean_dec_ref_known(v_x_4310_, 2);
            v___x_4317_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1___lam__0(v_head_4316_);
            v___x_4318_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1_spec__2(v_x_4311_, v___x_4317_, v_tail_4313_);
            return v___x_4318_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4320_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__0;
    v___x_4321_ = lean_string_length(v___x_4320_);
    return v___x_4321_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4322_ = crate::leanh::lean_obj_once(
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
    mut v_xs_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    v___x_4333_ = lean_array_get_size(v_xs_4332_);
    v___x_4334_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4335_ = lean_nat_dec_eq(v___x_4333_, v___x_4334_);
    if v___x_4335_ == 0 {
        let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4336_ = lean_array_to_list(v_xs_4332_);
        v___x_4337_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__3;
        v___x_4338_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1_spec__1(v___x_4336_, v___x_4337_);
        v___x_4339_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6_once
            ),
            _init_l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__6,
        );
        v___x_4340_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__7;
        v___x_4341_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4341_, 0, v___x_4340_);
        crate::leanh::lean_ctor_set(v___x_4341_, 1, v___x_4338_);
        v___x_4342_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__8;
        v___x_4343_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4343_, 0, v___x_4341_);
        crate::leanh::lean_ctor_set(v___x_4343_, 1, v___x_4342_);
        v___x_4344_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4344_, 0, v___x_4339_);
        crate::leanh::lean_ctor_set(v___x_4344_, 1, v___x_4343_);
        v___x_4345_ = l_Std_Format_fill(v___x_4344_);
        return v___x_4345_;
    } else {
        let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_4332_);
        v___x_4346_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__10;
        return v___x_4346_;
    }
}
pub unsafe fn l_Lean_IR_instReprIRType_repr(
    mut v_x_4353_: *mut crate::leanh::LeanObject,
    mut v_prec_4354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: u8 = 0;
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: u8 = 0;
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: u8 = 0;
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: u8 = 0;
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: u8 = 0;
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: u8 = 0;
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: u8 = 0;
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: u8 = 0;
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: u8 = 0;
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: u8 = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: u8 = 0;
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: u8 = 0;
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: u8 = 0;
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leanTypeName_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_types_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v___y_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_leanTypeName_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_types_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___y_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: u8 = 0;
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: u8 = 0;
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: u8 = 0;
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4353_) {
                0 => {
                    v___x_4439_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4440_ = lean_nat_dec_le(v___x_4439_, v_prec_4354_);
                    if v___x_4440_ == 0 {
                        v___x_4441_ = crate::leanh::lean_obj_once(
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
                        v___x_4442_ = crate::leanh::lean_obj_once(
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
                    v___x_4443_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4444_ = lean_nat_dec_le(v___x_4443_, v_prec_4354_);
                    if v___x_4444_ == 0 {
                        v___x_4445_ = crate::leanh::lean_obj_once(
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
                        v___x_4446_ = crate::leanh::lean_obj_once(
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
                    v___x_4447_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4448_ = lean_nat_dec_le(v___x_4447_, v_prec_4354_);
                    if v___x_4448_ == 0 {
                        v___x_4449_ = crate::leanh::lean_obj_once(
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
                        v___x_4450_ = crate::leanh::lean_obj_once(
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
                    v___x_4451_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4452_ = lean_nat_dec_le(v___x_4451_, v_prec_4354_);
                    if v___x_4452_ == 0 {
                        v___x_4453_ = crate::leanh::lean_obj_once(
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
                        v___x_4454_ = crate::leanh::lean_obj_once(
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
                    v___x_4455_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4456_ = lean_nat_dec_le(v___x_4455_, v_prec_4354_);
                    if v___x_4456_ == 0 {
                        v___x_4457_ = crate::leanh::lean_obj_once(
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
                        v___x_4458_ = crate::leanh::lean_obj_once(
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
                    v___x_4459_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4460_ = lean_nat_dec_le(v___x_4459_, v_prec_4354_);
                    if v___x_4460_ == 0 {
                        v___x_4461_ = crate::leanh::lean_obj_once(
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
                        v___x_4462_ = crate::leanh::lean_obj_once(
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
                    v___x_4463_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4464_ = lean_nat_dec_le(v___x_4463_, v_prec_4354_);
                    if v___x_4464_ == 0 {
                        v___x_4465_ = crate::leanh::lean_obj_once(
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
                        v___x_4466_ = crate::leanh::lean_obj_once(
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
                    v___x_4467_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4468_ = lean_nat_dec_le(v___x_4467_, v_prec_4354_);
                    if v___x_4468_ == 0 {
                        v___x_4469_ = crate::leanh::lean_obj_once(
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
                        v___x_4470_ = crate::leanh::lean_obj_once(
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
                    v___x_4471_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4472_ = lean_nat_dec_le(v___x_4471_, v_prec_4354_);
                    if v___x_4472_ == 0 {
                        v___x_4473_ = crate::leanh::lean_obj_once(
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
                        v___x_4474_ = crate::leanh::lean_obj_once(
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
                    v___x_4475_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4476_ = lean_nat_dec_le(v___x_4475_, v_prec_4354_);
                    if v___x_4476_ == 0 {
                        v___x_4477_ = crate::leanh::lean_obj_once(
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
                        v___x_4478_ = crate::leanh::lean_obj_once(
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
                    v_leanTypeName_4479_ = crate::leanh::lean_ctor_get(v_x_4353_, 0);
                    v_types_4480_ = crate::leanh::lean_ctor_get(v_x_4353_, 1);
                    v_isSharedCheck_4504_ = (!crate::leanh::lean_is_exclusive(v_x_4353_)) as u8;
                    if v_isSharedCheck_4504_ == 0 {
                        v___x_4482_ = v_x_4353_;
                        v_isShared_4483_ = v_isSharedCheck_4504_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_types_4480_);
                        crate::leanh::lean_inc(v_leanTypeName_4479_);
                        crate::leanh::lean_dec(v_x_4353_);
                        v___x_4482_ = crate::leanh::lean_box(0);
                        v_isShared_4483_ = v_isSharedCheck_4504_;
                        state = 13;
                        continue;
                    }
                }
                11 => {
                    v_leanTypeName_4505_ = crate::leanh::lean_ctor_get(v_x_4353_, 0);
                    v_types_4506_ = crate::leanh::lean_ctor_get(v_x_4353_, 1);
                    v_isSharedCheck_4530_ = (!crate::leanh::lean_is_exclusive(v_x_4353_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4508_ = v_x_4353_;
                        v_isShared_4509_ = v_isSharedCheck_4530_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_types_4506_);
                        crate::leanh::lean_inc(v_leanTypeName_4505_);
                        crate::leanh::lean_dec(v_x_4353_);
                        v___x_4508_ = crate::leanh::lean_box(0);
                        v_isShared_4509_ = v_isSharedCheck_4530_;
                        state = 16;
                        continue;
                    }
                }
                12 => {
                    v___x_4531_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4532_ = lean_nat_dec_le(v___x_4531_, v_prec_4354_);
                    if v___x_4532_ == 0 {
                        v___x_4533_ = crate::leanh::lean_obj_once(
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
                        v___x_4534_ = crate::leanh::lean_obj_once(
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
                    v___x_4535_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4536_ = lean_nat_dec_le(v___x_4535_, v_prec_4354_);
                    if v___x_4536_ == 0 {
                        v___x_4537_ = crate::leanh::lean_obj_once(
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
                        v___x_4538_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_inc(v___y_4356_);
                v___x_4358_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4358_, 0, v___y_4356_);
                crate::leanh::lean_ctor_set(v___x_4358_, 1, v___x_4357_);
                v___x_4359_ = 0;
                v___x_4360_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4360_, 0, v___x_4358_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4360_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4359_,
                );
                v___x_4361_ = l_Repr_addAppParen(v___x_4360_, v_prec_4354_);
                return v___x_4361_;
            }
            2 => {
                v___x_4364_ = l_Lean_IR_instReprIRType_repr___closed__3;
                crate::leanh::lean_inc(v___y_4363_);
                v___x_4365_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4365_, 0, v___y_4363_);
                crate::leanh::lean_ctor_set(v___x_4365_, 1, v___x_4364_);
                v___x_4366_ = 0;
                v___x_4367_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4367_, 0, v___x_4365_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4367_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4366_,
                );
                v___x_4368_ = l_Repr_addAppParen(v___x_4367_, v_prec_4354_);
                return v___x_4368_;
            }
            3 => {
                v___x_4371_ = l_Lean_IR_instReprIRType_repr___closed__5;
                crate::leanh::lean_inc(v___y_4370_);
                v___x_4372_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4372_, 0, v___y_4370_);
                crate::leanh::lean_ctor_set(v___x_4372_, 1, v___x_4371_);
                v___x_4373_ = 0;
                v___x_4374_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4372_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4374_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4373_,
                );
                v___x_4375_ = l_Repr_addAppParen(v___x_4374_, v_prec_4354_);
                return v___x_4375_;
            }
            4 => {
                v___x_4378_ = l_Lean_IR_instReprIRType_repr___closed__7;
                crate::leanh::lean_inc(v___y_4377_);
                v___x_4379_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4379_, 0, v___y_4377_);
                crate::leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
                v___x_4380_ = 0;
                v___x_4381_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4381_, 0, v___x_4379_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4381_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4380_,
                );
                v___x_4382_ = l_Repr_addAppParen(v___x_4381_, v_prec_4354_);
                return v___x_4382_;
            }
            5 => {
                v___x_4385_ = l_Lean_IR_instReprIRType_repr___closed__9;
                crate::leanh::lean_inc(v___y_4384_);
                v___x_4386_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4386_, 0, v___y_4384_);
                crate::leanh::lean_ctor_set(v___x_4386_, 1, v___x_4385_);
                v___x_4387_ = 0;
                v___x_4388_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4388_, 0, v___x_4386_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4388_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4387_,
                );
                v___x_4389_ = l_Repr_addAppParen(v___x_4388_, v_prec_4354_);
                return v___x_4389_;
            }
            6 => {
                v___x_4392_ = l_Lean_IR_instReprIRType_repr___closed__11;
                crate::leanh::lean_inc(v___y_4391_);
                v___x_4393_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4393_, 0, v___y_4391_);
                crate::leanh::lean_ctor_set(v___x_4393_, 1, v___x_4392_);
                v___x_4394_ = 0;
                v___x_4395_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4395_, 0, v___x_4393_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4394_,
                );
                v___x_4396_ = l_Repr_addAppParen(v___x_4395_, v_prec_4354_);
                return v___x_4396_;
            }
            7 => {
                v___x_4399_ = l_Lean_IR_instReprIRType_repr___closed__13;
                crate::leanh::lean_inc(v___y_4398_);
                v___x_4400_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4400_, 0, v___y_4398_);
                crate::leanh::lean_ctor_set(v___x_4400_, 1, v___x_4399_);
                v___x_4401_ = 0;
                v___x_4402_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4402_, 0, v___x_4400_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4402_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4401_,
                );
                v___x_4403_ = l_Repr_addAppParen(v___x_4402_, v_prec_4354_);
                return v___x_4403_;
            }
            8 => {
                v___x_4406_ = l_Lean_IR_instReprIRType_repr___closed__15;
                crate::leanh::lean_inc(v___y_4405_);
                v___x_4407_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4407_, 0, v___y_4405_);
                crate::leanh::lean_ctor_set(v___x_4407_, 1, v___x_4406_);
                v___x_4408_ = 0;
                v___x_4409_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4409_, 0, v___x_4407_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4409_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4408_,
                );
                v___x_4410_ = l_Repr_addAppParen(v___x_4409_, v_prec_4354_);
                return v___x_4410_;
            }
            9 => {
                v___x_4413_ = l_Lean_IR_instReprIRType_repr___closed__17;
                crate::leanh::lean_inc(v___y_4412_);
                v___x_4414_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4414_, 0, v___y_4412_);
                crate::leanh::lean_ctor_set(v___x_4414_, 1, v___x_4413_);
                v___x_4415_ = 0;
                v___x_4416_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4416_, 0, v___x_4414_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4416_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4415_,
                );
                v___x_4417_ = l_Repr_addAppParen(v___x_4416_, v_prec_4354_);
                return v___x_4417_;
            }
            10 => {
                v___x_4420_ = l_Lean_IR_instReprIRType_repr___closed__19;
                crate::leanh::lean_inc(v___y_4419_);
                v___x_4421_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4421_, 0, v___y_4419_);
                crate::leanh::lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                v___x_4422_ = 0;
                v___x_4423_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4423_, 0, v___x_4421_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4423_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4422_,
                );
                v___x_4424_ = l_Repr_addAppParen(v___x_4423_, v_prec_4354_);
                return v___x_4424_;
            }
            11 => {
                v___x_4427_ = l_Lean_IR_instReprIRType_repr___closed__21;
                crate::leanh::lean_inc(v___y_4426_);
                v___x_4428_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4428_, 0, v___y_4426_);
                crate::leanh::lean_ctor_set(v___x_4428_, 1, v___x_4427_);
                v___x_4429_ = 0;
                v___x_4430_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4430_, 0, v___x_4428_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4430_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4429_,
                );
                v___x_4431_ = l_Repr_addAppParen(v___x_4430_, v_prec_4354_);
                return v___x_4431_;
            }
            12 => {
                v___x_4434_ = l_Lean_IR_instReprIRType_repr___closed__23;
                crate::leanh::lean_inc(v___y_4433_);
                v___x_4435_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4435_, 0, v___y_4433_);
                crate::leanh::lean_ctor_set(v___x_4435_, 1, v___x_4434_);
                v___x_4436_ = 0;
                v___x_4437_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4437_, 0, v___x_4435_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4437_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4436_,
                );
                v___x_4438_ = l_Repr_addAppParen(v___x_4437_, v_prec_4354_);
                return v___x_4438_;
            }
            13 => {
                v___x_4500_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4501_ = lean_nat_dec_le(v___x_4500_, v_prec_4354_);
                if v___x_4501_ == 0 {
                    v___x_4502_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24_once),
                        _init_l_Lean_IR_instReprIRType_repr___closed__24,
                    );
                    v___y_4485_ = v___x_4502_;
                    state = 14;
                    continue;
                } else {
                    v___x_4503_ = crate::leanh::lean_obj_once(
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
                v___x_4486_ = crate::leanh::lean_box(1);
                v___x_4487_ = l_Lean_IR_instReprIRType_repr___closed__28;
                v___x_4488_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4489_ = l_Option_repr___at___00Lean_IR_instReprIRType_repr_spec__0(
                    v_leanTypeName_4479_,
                    v___x_4488_,
                );
                if v_isShared_4483_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4482_, 5);
                    crate::leanh::lean_ctor_set(v___x_4482_, 1, v___x_4489_);
                    crate::leanh::lean_ctor_set(v___x_4482_, 0, v___x_4487_);
                    v___x_4491_ = v___x_4482_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4499_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 1, v___x_4489_);
                    v___x_4491_ = v_reuseFailAlloc_4499_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4492_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4492_, 0, v___x_4491_);
                crate::leanh::lean_ctor_set(v___x_4492_, 1, v___x_4486_);
                v___x_4493_ =
                    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_4480_);
                v___x_4494_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4494_, 0, v___x_4492_);
                crate::leanh::lean_ctor_set(v___x_4494_, 1, v___x_4493_);
                crate::leanh::lean_inc(v___y_4485_);
                v___x_4495_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4495_, 0, v___y_4485_);
                crate::leanh::lean_ctor_set(v___x_4495_, 1, v___x_4494_);
                v___x_4496_ = 0;
                v___x_4497_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4497_, 0, v___x_4495_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4497_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4496_,
                );
                v___x_4498_ = l_Repr_addAppParen(v___x_4497_, v_prec_4354_);
                return v___x_4498_;
            }
            16 => {
                v___x_4526_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4527_ = lean_nat_dec_le(v___x_4526_, v_prec_4354_);
                if v___x_4527_ == 0 {
                    v___x_4528_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24),
                        core::ptr::addr_of_mut!(l_Lean_IR_instReprIRType_repr___closed__24_once),
                        _init_l_Lean_IR_instReprIRType_repr___closed__24,
                    );
                    v___y_4511_ = v___x_4528_;
                    state = 17;
                    continue;
                } else {
                    v___x_4529_ = crate::leanh::lean_obj_once(
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
                v___x_4512_ = crate::leanh::lean_box(1);
                v___x_4513_ = l_Lean_IR_instReprIRType_repr___closed__31;
                v___x_4514_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_4515_ = l_Lean_Name_reprPrec(v_leanTypeName_4505_, v___x_4514_);
                if v_isShared_4509_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4508_, 5);
                    crate::leanh::lean_ctor_set(v___x_4508_, 1, v___x_4515_);
                    crate::leanh::lean_ctor_set(v___x_4508_, 0, v___x_4513_);
                    v___x_4517_ = v___x_4508_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4525_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4525_, 1, v___x_4515_);
                    v___x_4517_ = v_reuseFailAlloc_4525_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4518_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4518_, 0, v___x_4517_);
                crate::leanh::lean_ctor_set(v___x_4518_, 1, v___x_4512_);
                v___x_4519_ =
                    l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1(v_types_4506_);
                v___x_4520_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4520_, 0, v___x_4518_);
                crate::leanh::lean_ctor_set(v___x_4520_, 1, v___x_4519_);
                crate::leanh::lean_inc(v___y_4511_);
                v___x_4521_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4521_, 0, v___y_4511_);
                crate::leanh::lean_ctor_set(v___x_4521_, 1, v___x_4520_);
                v___x_4522_ = 0;
                v___x_4523_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4523_, 0, v___x_4521_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4523_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v___y_4539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4540_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4541_ = l_Lean_IR_instReprIRType_repr(v___y_4539_, v___x_4540_);
    return v___x_4541_;
}
pub unsafe fn l_Lean_IR_instReprIRType_repr___boxed(
    mut v_x_4542_: *mut crate::leanh::LeanObject,
    mut v_prec_4543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4544_ = l_Lean_IR_instReprIRType_repr(v_x_4542_, v_prec_4543_);
    crate::leanh::lean_dec(v_prec_4543_);
    return v_res_4544_;
}
pub unsafe fn l_Lean_IR_IRType_isScalar(mut v_x_4547_: *mut crate::leanh::LeanObject) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_4547_) {
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
pub unsafe fn l_Lean_IR_IRType_isScalar___boxed(
    mut v_x_4556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4557_: u8 = 0;
    let mut v_r_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4557_ = l_Lean_IR_IRType_isScalar(v_x_4556_);
    crate::leanh::lean_dec(v_x_4556_);
    v_r_4558_ = crate::leanh::lean_box((v_res_4557_) as usize);
    return v_r_4558_;
}
pub unsafe fn l_Lean_IR_IRType_isObj(mut v_x_4559_: *mut crate::leanh::LeanObject) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_4559_) {
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
pub unsafe fn l_Lean_IR_IRType_isObj___boxed(
    mut v_x_4565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4566_: u8 = 0;
    let mut v_r_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4566_ = l_Lean_IR_IRType_isObj(v_x_4565_);
    crate::leanh::lean_dec(v_x_4565_);
    v_r_4567_ = crate::leanh::lean_box((v_res_4566_) as usize);
    return v_r_4567_;
}
pub unsafe fn l_Lean_IR_IRType_isPossibleRef(mut v_x_4568_: *mut crate::leanh::LeanObject) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_4568_) {
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
    mut v_x_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4573_: u8 = 0;
    let mut v_r_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4573_ = l_Lean_IR_IRType_isPossibleRef(v_x_4572_);
    crate::leanh::lean_dec(v_x_4572_);
    v_r_4574_ = crate::leanh::lean_box((v_res_4573_) as usize);
    return v_r_4574_;
}
pub unsafe fn l_Lean_IR_IRType_isDefiniteRef(mut v_x_4575_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4575_) == 7 {
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
    mut v_x_4578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4579_: u8 = 0;
    let mut v_r_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4579_ = l_Lean_IR_IRType_isDefiniteRef(v_x_4578_);
    crate::leanh::lean_dec(v_x_4578_);
    v_r_4580_ = crate::leanh::lean_box((v_res_4579_) as usize);
    return v_r_4580_;
}
pub unsafe fn l_Lean_IR_IRType_isErased(mut v_x_4581_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4581_) == 6 {
        let mut v___x_4582_: u8 = 0;
        v___x_4582_ = 1;
        return v___x_4582_;
    } else {
        let mut v___x_4583_: u8 = 0;
        v___x_4583_ = 0;
        return v___x_4583_;
    }
}
pub unsafe fn l_Lean_IR_IRType_isErased___boxed(
    mut v_x_4584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4585_: u8 = 0;
    let mut v_r_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4585_ = l_Lean_IR_IRType_isErased(v_x_4584_);
    crate::leanh::lean_dec(v_x_4584_);
    v_r_4586_ = crate::leanh::lean_box((v_res_4585_) as usize);
    return v_r_4586_;
}
pub unsafe fn l_Lean_IR_IRType_isVoid(mut v_x_4587_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4587_) == 13 {
        let mut v___x_4588_: u8 = 0;
        v___x_4588_ = 1;
        return v___x_4588_;
    } else {
        let mut v___x_4589_: u8 = 0;
        v___x_4589_ = 0;
        return v___x_4589_;
    }
}
pub unsafe fn l_Lean_IR_IRType_isVoid___boxed(
    mut v_x_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4591_: u8 = 0;
    let mut v_r_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4591_ = l_Lean_IR_IRType_isVoid(v_x_4590_);
    crate::leanh::lean_dec(v_x_4590_);
    v_r_4592_ = crate::leanh::lean_box((v_res_4591_) as usize);
    return v_r_4592_;
}
pub unsafe fn l_Lean_IR_IRType_boxed(
    mut v_x_4593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4593_) {
        7 => {
            return v_x_4593_;
        }
        0 => {
            let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4594_ = crate::leanh::lean_box(7);
            return v___x_4594_;
        }
        9 => {
            let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4595_ = crate::leanh::lean_box(7);
            return v___x_4595_;
        }
        13 => {
            let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4596_ = crate::leanh::lean_box(12);
            return v___x_4596_;
        }
        12 => {
            return v_x_4593_;
        }
        1 => {
            let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4597_ = crate::leanh::lean_box(12);
            return v___x_4597_;
        }
        2 => {
            let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4598_ = crate::leanh::lean_box(12);
            return v___x_4598_;
        }
        _ => {
            let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4599_ = crate::leanh::lean_box(8);
            return v___x_4599_;
        }
    }
}
pub unsafe fn l_Lean_IR_IRType_boxed___boxed(
    mut v_x_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4601_ = l_Lean_IR_IRType_boxed(v_x_4600_);
    crate::leanh::lean_dec(v_x_4600_);
    return v_res_4601_;
}
pub unsafe fn l_Lean_IR_Arg_ctorIdx(
    mut v_x_4602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4602_) == 0 {
        let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4603_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4603_;
    } else {
        let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4604_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_4604_;
    }
}
pub unsafe fn l_Lean_IR_Arg_ctorIdx___boxed(
    mut v_x_4605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l_Lean_IR_Arg_ctorIdx(v_x_4605_);
    crate::leanh::lean_dec(v_x_4605_);
    return v_res_4606_;
}
pub unsafe fn l_Lean_IR_Arg_ctorElim___redArg(
    mut v_t_4607_: *mut crate::leanh::LeanObject,
    mut v_k_4608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4607_) == 0 {
        let mut v_id_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_id_4609_ = crate::leanh::lean_ctor_get(v_t_4607_, 0);
        crate::leanh::lean_inc(v_id_4609_);
        crate::leanh::lean_dec_ref_known(v_t_4607_, 1);
        v___x_4610_ = crate::leanh::lean_apply_1(v_k_4608_, v_id_4609_);
        return v___x_4610_;
    } else {
        return v_k_4608_;
    }
}
pub unsafe fn l_Lean_IR_Arg_ctorElim(
    mut v_motive_4611_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4612_: *mut crate::leanh::LeanObject,
    mut v_t_4613_: *mut crate::leanh::LeanObject,
    mut v_h_4614_: *mut crate::leanh::LeanObject,
    mut v_k_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4616_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4613_, v_k_4615_);
    return v___x_4616_;
}
pub unsafe fn l_Lean_IR_Arg_ctorElim___boxed(
    mut v_motive_4617_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4618_: *mut crate::leanh::LeanObject,
    mut v_t_4619_: *mut crate::leanh::LeanObject,
    mut v_h_4620_: *mut crate::leanh::LeanObject,
    mut v_k_4621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4622_ = l_Lean_IR_Arg_ctorElim(
        v_motive_4617_,
        v_ctorIdx_4618_,
        v_t_4619_,
        v_h_4620_,
        v_k_4621_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4618_);
    return v_res_4622_;
}
pub unsafe fn l_Lean_IR_Arg_var_elim___redArg(
    mut v_t_4623_: *mut crate::leanh::LeanObject,
    mut v_var_4624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4623_, v_var_4624_);
    return v___x_4625_;
}
pub unsafe fn l_Lean_IR_Arg_var_elim(
    mut v_motive_4626_: *mut crate::leanh::LeanObject,
    mut v_t_4627_: *mut crate::leanh::LeanObject,
    mut v_h_4628_: *mut crate::leanh::LeanObject,
    mut v_var_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4627_, v_var_4629_);
    return v___x_4630_;
}
pub unsafe fn l_Lean_IR_Arg_erased_elim___redArg(
    mut v_t_4631_: *mut crate::leanh::LeanObject,
    mut v_erased_4632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4633_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4631_, v_erased_4632_);
    return v___x_4633_;
}
pub unsafe fn l_Lean_IR_Arg_erased_elim(
    mut v_motive_4634_: *mut crate::leanh::LeanObject,
    mut v_t_4635_: *mut crate::leanh::LeanObject,
    mut v_h_4636_: *mut crate::leanh::LeanObject,
    mut v_erased_4637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4638_ = l_Lean_IR_Arg_ctorElim___redArg(v_t_4635_, v_erased_4637_);
    return v___x_4638_;
}
pub unsafe fn l_Lean_IR_instBEqArg_beq(
    mut v_x_4643_: *mut crate::leanh::LeanObject,
    mut v_x_4644_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4643_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4644_) == 0 {
            let mut v_id_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4647_: u8 = 0;
            v_id_4645_ = crate::leanh::lean_ctor_get(v_x_4643_, 0);
            v_id_4646_ = crate::leanh::lean_ctor_get(v_x_4644_, 0);
            v___x_4647_ = lean_nat_dec_eq(v_id_4645_, v_id_4646_);
            return v___x_4647_;
        } else {
            let mut v___x_4648_: u8 = 0;
            v___x_4648_ = 0;
            return v___x_4648_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4644_) == 1 {
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
    mut v_x_4651_: *mut crate::leanh::LeanObject,
    mut v_x_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: u8 = 0;
    let mut v_r_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_IR_instBEqArg_beq(v_x_4651_, v_x_4652_);
    crate::leanh::lean_dec(v_x_4652_);
    crate::leanh::lean_dec(v_x_4651_);
    v_r_4654_ = crate::leanh::lean_box((v_res_4653_) as usize);
    return v_r_4654_;
}
pub unsafe fn l_Lean_IR_instReprArg_repr(
    mut v_x_4666_: *mut crate::leanh::LeanObject,
    mut v_prec_4667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: u8 = 0;
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: u8 = 0;
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4666_) == 0 {
                    v_id_4675_ = crate::leanh::lean_ctor_get(v_x_4666_, 0);
                    crate::leanh::lean_inc(v_id_4675_);
                    crate::leanh::lean_dec_ref_known(v_x_4666_, 1);
                    v___x_4685_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4686_ = lean_nat_dec_le(v___x_4685_, v_prec_4667_);
                    if v___x_4686_ == 0 {
                        v___x_4687_ = crate::leanh::lean_obj_once(
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
                        v___x_4688_ = crate::leanh::lean_obj_once(
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
                    v___x_4689_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_4690_ = lean_nat_dec_le(v___x_4689_, v_prec_4667_);
                    if v___x_4690_ == 0 {
                        v___x_4691_ = crate::leanh::lean_obj_once(
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
                        v___x_4692_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_inc(v___y_4669_);
                v___x_4671_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4671_, 0, v___y_4669_);
                crate::leanh::lean_ctor_set(v___x_4671_, 1, v___x_4670_);
                v___x_4672_ = 0;
                v___x_4673_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4673_, 0, v___x_4671_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4673_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4672_,
                );
                v___x_4674_ = l_Repr_addAppParen(v___x_4673_, v_prec_4667_);
                return v___x_4674_;
            }
            2 => {
                v___x_4678_ = l_Lean_IR_instReprArg_repr___closed__4;
                v___x_4679_ = l_Lean_IR_instReprVarId_repr___redArg(v_id_4675_);
                v___x_4680_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4678_);
                crate::leanh::lean_ctor_set(v___x_4680_, 1, v___x_4679_);
                crate::leanh::lean_inc(v___y_4677_);
                v___x_4681_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4681_, 0, v___y_4677_);
                crate::leanh::lean_ctor_set(v___x_4681_, 1, v___x_4680_);
                v___x_4682_ = 0;
                v___x_4683_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4683_, 0, v___x_4681_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4683_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_4693_: *mut crate::leanh::LeanObject,
    mut v_prec_4694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4695_ = l_Lean_IR_instReprArg_repr(v_x_4693_, v_prec_4694_);
    crate::leanh::lean_dec(v_prec_4694_);
    return v_res_4695_;
}
pub unsafe fn l_Lean_IR_Arg_beq(
    mut v_x_4698_: *mut crate::leanh::LeanObject,
    mut v_x_4699_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4698_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4699_) == 0 {
            let mut v_id_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4702_: u8 = 0;
            v_id_4700_ = crate::leanh::lean_ctor_get(v_x_4698_, 0);
            v_id_4701_ = crate::leanh::lean_ctor_get(v_x_4699_, 0);
            v___x_4702_ = lean_nat_dec_eq(v_id_4700_, v_id_4701_);
            return v___x_4702_;
        } else {
            let mut v___x_4703_: u8 = 0;
            v___x_4703_ = 0;
            return v___x_4703_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4699_) == 1 {
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
    mut v_x_4706_: *mut crate::leanh::LeanObject,
    mut v_x_4707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4708_: u8 = 0;
    let mut v_r_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4708_ = l_Lean_IR_Arg_beq(v_x_4706_, v_x_4707_);
    crate::leanh::lean_dec(v_x_4707_);
    crate::leanh::lean_dec(v_x_4706_);
    v_r_4709_ = crate::leanh::lean_box((v_res_4708_) as usize);
    return v_r_4709_;
}
pub unsafe fn l_Lean_IR_LitVal_ctorIdx(
    mut v_x_4710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4710_) == 0 {
        let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4711_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_4711_;
    } else {
        let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4712_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_4712_;
    }
}
pub unsafe fn l_Lean_IR_LitVal_ctorIdx___boxed(
    mut v_x_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4714_ = l_Lean_IR_LitVal_ctorIdx(v_x_4713_);
    crate::leanh::lean_dec_ref(v_x_4713_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_IR_LitVal_ctorElim___redArg(
    mut v_t_4715_: *mut crate::leanh::LeanObject,
    mut v_k_4716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4715_) == 0 {
        let mut v_v_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_4717_ = crate::leanh::lean_ctor_get(v_t_4715_, 0);
        crate::leanh::lean_inc(v_v_4717_);
        crate::leanh::lean_dec_ref_known(v_t_4715_, 1);
        v___x_4718_ = crate::leanh::lean_apply_1(v_k_4716_, v_v_4717_);
        return v___x_4718_;
    } else {
        let mut v_v_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_4719_ = crate::leanh::lean_ctor_get(v_t_4715_, 0);
        crate::leanh::lean_inc_ref(v_v_4719_);
        crate::leanh::lean_dec_ref_known(v_t_4715_, 1);
        v___x_4720_ = crate::leanh::lean_apply_1(v_k_4716_, v_v_4719_);
        return v___x_4720_;
    }
}
pub unsafe fn l_Lean_IR_LitVal_ctorElim(
    mut v_motive_4721_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4722_: *mut crate::leanh::LeanObject,
    mut v_t_4723_: *mut crate::leanh::LeanObject,
    mut v_h_4724_: *mut crate::leanh::LeanObject,
    mut v_k_4725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4726_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4723_, v_k_4725_);
    return v___x_4726_;
}
pub unsafe fn l_Lean_IR_LitVal_ctorElim___boxed(
    mut v_motive_4727_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4728_: *mut crate::leanh::LeanObject,
    mut v_t_4729_: *mut crate::leanh::LeanObject,
    mut v_h_4730_: *mut crate::leanh::LeanObject,
    mut v_k_4731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4732_ = l_Lean_IR_LitVal_ctorElim(
        v_motive_4727_,
        v_ctorIdx_4728_,
        v_t_4729_,
        v_h_4730_,
        v_k_4731_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4728_);
    return v_res_4732_;
}
pub unsafe fn l_Lean_IR_LitVal_num_elim___redArg(
    mut v_t_4733_: *mut crate::leanh::LeanObject,
    mut v_num_4734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4735_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4733_, v_num_4734_);
    return v___x_4735_;
}
pub unsafe fn l_Lean_IR_LitVal_num_elim(
    mut v_motive_4736_: *mut crate::leanh::LeanObject,
    mut v_t_4737_: *mut crate::leanh::LeanObject,
    mut v_h_4738_: *mut crate::leanh::LeanObject,
    mut v_num_4739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4740_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4737_, v_num_4739_);
    return v___x_4740_;
}
pub unsafe fn l_Lean_IR_LitVal_str_elim___redArg(
    mut v_t_4741_: *mut crate::leanh::LeanObject,
    mut v_str_4742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4743_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4741_, v_str_4742_);
    return v___x_4743_;
}
pub unsafe fn l_Lean_IR_LitVal_str_elim(
    mut v_motive_4744_: *mut crate::leanh::LeanObject,
    mut v_t_4745_: *mut crate::leanh::LeanObject,
    mut v_h_4746_: *mut crate::leanh::LeanObject,
    mut v_str_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4748_ = l_Lean_IR_LitVal_ctorElim___redArg(v_t_4745_, v_str_4747_);
    return v___x_4748_;
}
pub unsafe fn l_Lean_IR_instBEqLitVal_beq(
    mut v_x_4753_: *mut crate::leanh::LeanObject,
    mut v_x_4754_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4753_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_4754_) == 0 {
            let mut v_v_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4757_: u8 = 0;
            v_v_4755_ = crate::leanh::lean_ctor_get(v_x_4753_, 0);
            v_v_4756_ = crate::leanh::lean_ctor_get(v_x_4754_, 0);
            v___x_4757_ = lean_nat_dec_eq(v_v_4755_, v_v_4756_);
            return v___x_4757_;
        } else {
            let mut v___x_4758_: u8 = 0;
            v___x_4758_ = 0;
            return v___x_4758_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_4754_) == 1 {
            let mut v_v_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4761_: u8 = 0;
            v_v_4759_ = crate::leanh::lean_ctor_get(v_x_4753_, 0);
            v_v_4760_ = crate::leanh::lean_ctor_get(v_x_4754_, 0);
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
    mut v_x_4763_: *mut crate::leanh::LeanObject,
    mut v_x_4764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4765_: u8 = 0;
    let mut v_r_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4765_ = l_Lean_IR_instBEqLitVal_beq(v_x_4763_, v_x_4764_);
    crate::leanh::lean_dec_ref(v_x_4764_);
    crate::leanh::lean_dec_ref(v_x_4763_);
    v_r_4766_ = crate::leanh::lean_box((v_res_4765_) as usize);
    return v_r_4766_;
}
pub unsafe fn l_Lean_IR_instBEqCtorInfo_beq(
    mut v_x_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    v_name_4776_ = crate::leanh::lean_ctor_get(v_x_4774_, 0);
    v_cidx_4777_ = crate::leanh::lean_ctor_get(v_x_4774_, 1);
    v_size_4778_ = crate::leanh::lean_ctor_get(v_x_4774_, 2);
    v_usize_4779_ = crate::leanh::lean_ctor_get(v_x_4774_, 3);
    v_ssize_4780_ = crate::leanh::lean_ctor_get(v_x_4774_, 4);
    v_name_4781_ = crate::leanh::lean_ctor_get(v_x_4775_, 0);
    v_cidx_4782_ = crate::leanh::lean_ctor_get(v_x_4775_, 1);
    v_size_4783_ = crate::leanh::lean_ctor_get(v_x_4775_, 2);
    v_usize_4784_ = crate::leanh::lean_ctor_get(v_x_4775_, 3);
    v_ssize_4785_ = crate::leanh::lean_ctor_get(v_x_4775_, 4);
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
    mut v_x_4791_: *mut crate::leanh::LeanObject,
    mut v_x_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4793_: u8 = 0;
    let mut v_r_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4793_ = l_Lean_IR_instBEqCtorInfo_beq(v_x_4791_, v_x_4792_);
    crate::leanh::lean_dec_ref(v_x_4792_);
    crate::leanh::lean_dec_ref(v_x_4791_);
    v_r_4794_ = crate::leanh::lean_box((v_res_4793_) as usize);
    return v_r_4794_;
}
pub unsafe fn _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4806_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_4807_ = lean_nat_to_int(v___x_4806_);
    return v___x_4807_;
}
pub unsafe fn _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4817_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_4818_ = lean_nat_to_int(v___x_4817_);
    return v___x_4818_;
}
pub unsafe fn l_Lean_IR_instReprCtorInfo_repr___redArg(
    mut v_x_4822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: u8 = 0;
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4823_ = crate::leanh::lean_ctor_get(v_x_4822_, 0);
    crate::leanh::lean_inc(v_name_4823_);
    v_cidx_4824_ = crate::leanh::lean_ctor_get(v_x_4822_, 1);
    crate::leanh::lean_inc(v_cidx_4824_);
    v_size_4825_ = crate::leanh::lean_ctor_get(v_x_4822_, 2);
    crate::leanh::lean_inc(v_size_4825_);
    v_usize_4826_ = crate::leanh::lean_ctor_get(v_x_4822_, 3);
    crate::leanh::lean_inc(v_usize_4826_);
    v_ssize_4827_ = crate::leanh::lean_ctor_get(v_x_4822_, 4);
    crate::leanh::lean_inc(v_ssize_4827_);
    crate::leanh::lean_dec_ref(v_x_4822_);
    v___x_4828_ = l_Lean_IR_instReprVarId_repr___redArg___closed__5;
    v___x_4829_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__3;
    v___x_4830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4_once),
        _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__4,
    );
    v___x_4831_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4832_ = l_Lean_Name_reprPrec(v_name_4823_, v___x_4831_);
    v___x_4833_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4833_, 0, v___x_4830_);
    crate::leanh::lean_ctor_set(v___x_4833_, 1, v___x_4832_);
    v___x_4834_ = 0;
    v___x_4835_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4835_, 0, v___x_4833_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4835_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4836_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4836_, 0, v___x_4829_);
    crate::leanh::lean_ctor_set(v___x_4836_, 1, v___x_4835_);
    v___x_4837_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2;
    v___x_4838_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4838_, 0, v___x_4836_);
    crate::leanh::lean_ctor_set(v___x_4838_, 1, v___x_4837_);
    v___x_4839_ = crate::leanh::lean_box(1);
    v___x_4840_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4840_, 0, v___x_4838_);
    crate::leanh::lean_ctor_set(v___x_4840_, 1, v___x_4839_);
    v___x_4841_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__6;
    v___x_4842_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4842_, 0, v___x_4840_);
    crate::leanh::lean_ctor_set(v___x_4842_, 1, v___x_4841_);
    v___x_4843_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4843_, 0, v___x_4842_);
    crate::leanh::lean_ctor_set(v___x_4843_, 1, v___x_4828_);
    v___x_4844_ = l_Nat_reprFast(v_cidx_4824_);
    v___x_4845_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4845_, 0, v___x_4844_);
    v___x_4846_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4846_, 0, v___x_4830_);
    crate::leanh::lean_ctor_set(v___x_4846_, 1, v___x_4845_);
    v___x_4847_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4847_, 0, v___x_4846_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4847_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4848_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4848_, 0, v___x_4843_);
    crate::leanh::lean_ctor_set(v___x_4848_, 1, v___x_4847_);
    v___x_4849_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4849_, 0, v___x_4848_);
    crate::leanh::lean_ctor_set(v___x_4849_, 1, v___x_4837_);
    v___x_4850_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4850_, 0, v___x_4849_);
    crate::leanh::lean_ctor_set(v___x_4850_, 1, v___x_4839_);
    v___x_4851_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__8;
    v___x_4852_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4852_, 0, v___x_4850_);
    crate::leanh::lean_ctor_set(v___x_4852_, 1, v___x_4851_);
    v___x_4853_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4853_, 0, v___x_4852_);
    crate::leanh::lean_ctor_set(v___x_4853_, 1, v___x_4828_);
    v___x_4854_ = l_Nat_reprFast(v_size_4825_);
    v___x_4855_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4855_, 0, v___x_4854_);
    v___x_4856_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4856_, 0, v___x_4830_);
    crate::leanh::lean_ctor_set(v___x_4856_, 1, v___x_4855_);
    v___x_4857_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4857_, 0, v___x_4856_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4857_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4858_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4858_, 0, v___x_4853_);
    crate::leanh::lean_ctor_set(v___x_4858_, 1, v___x_4857_);
    v___x_4859_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4859_, 0, v___x_4858_);
    crate::leanh::lean_ctor_set(v___x_4859_, 1, v___x_4837_);
    v___x_4860_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4860_, 0, v___x_4859_);
    crate::leanh::lean_ctor_set(v___x_4860_, 1, v___x_4839_);
    v___x_4861_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__10;
    v___x_4862_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4862_, 0, v___x_4860_);
    crate::leanh::lean_ctor_set(v___x_4862_, 1, v___x_4861_);
    v___x_4863_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4863_, 0, v___x_4862_);
    crate::leanh::lean_ctor_set(v___x_4863_, 1, v___x_4828_);
    v___x_4864_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11_once),
        _init_l_Lean_IR_instReprCtorInfo_repr___redArg___closed__11,
    );
    v___x_4865_ = l_Nat_reprFast(v_usize_4826_);
    v___x_4866_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4866_, 0, v___x_4865_);
    v___x_4867_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4867_, 0, v___x_4864_);
    crate::leanh::lean_ctor_set(v___x_4867_, 1, v___x_4866_);
    v___x_4868_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4868_, 0, v___x_4867_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4868_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4869_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4869_, 0, v___x_4863_);
    crate::leanh::lean_ctor_set(v___x_4869_, 1, v___x_4868_);
    v___x_4870_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4870_, 0, v___x_4869_);
    crate::leanh::lean_ctor_set(v___x_4870_, 1, v___x_4837_);
    v___x_4871_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4871_, 0, v___x_4870_);
    crate::leanh::lean_ctor_set(v___x_4871_, 1, v___x_4839_);
    v___x_4872_ = l_Lean_IR_instReprCtorInfo_repr___redArg___closed__13;
    v___x_4873_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4873_, 0, v___x_4871_);
    crate::leanh::lean_ctor_set(v___x_4873_, 1, v___x_4872_);
    v___x_4874_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4874_, 0, v___x_4873_);
    crate::leanh::lean_ctor_set(v___x_4874_, 1, v___x_4828_);
    v___x_4875_ = l_Nat_reprFast(v_ssize_4827_);
    v___x_4876_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4876_, 0, v___x_4875_);
    v___x_4877_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4877_, 0, v___x_4864_);
    crate::leanh::lean_ctor_set(v___x_4877_, 1, v___x_4876_);
    v___x_4878_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4878_, 0, v___x_4877_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4878_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    v___x_4879_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4879_, 0, v___x_4874_);
    crate::leanh::lean_ctor_set(v___x_4879_, 1, v___x_4878_);
    v___x_4880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_4881_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_4882_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4882_, 0, v___x_4881_);
    crate::leanh::lean_ctor_set(v___x_4882_, 1, v___x_4879_);
    v___x_4883_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_4884_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4884_, 0, v___x_4882_);
    crate::leanh::lean_ctor_set(v___x_4884_, 1, v___x_4883_);
    v___x_4885_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4885_, 0, v___x_4880_);
    crate::leanh::lean_ctor_set(v___x_4885_, 1, v___x_4884_);
    v___x_4886_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4886_, 0, v___x_4885_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4886_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4834_,
    );
    return v___x_4886_;
}
pub unsafe fn l_Lean_IR_instReprCtorInfo_repr(
    mut v_x_4887_: *mut crate::leanh::LeanObject,
    mut v_prec_4888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4889_ = l_Lean_IR_instReprCtorInfo_repr___redArg(v_x_4887_);
    return v___x_4889_;
}
pub unsafe fn l_Lean_IR_instReprCtorInfo_repr___boxed(
    mut v_x_4890_: *mut crate::leanh::LeanObject,
    mut v_prec_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4892_ = l_Lean_IR_instReprCtorInfo_repr(v_x_4890_, v_prec_4891_);
    crate::leanh::lean_dec(v_prec_4891_);
    return v_res_4892_;
}
pub unsafe fn l_Lean_IR_CtorInfo_isRef(mut v_info_4895_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_size_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usize_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ssize_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: u8 = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: u8 = 0;
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4896_ = crate::leanh::lean_ctor_get(v_info_4895_, 2);
                v_usize_4897_ = crate::leanh::lean_ctor_get(v_info_4895_, 3);
                v_ssize_4898_ = crate::leanh::lean_ctor_get(v_info_4895_, 4);
                v___x_4903_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v___x_4901_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_info_4906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4907_: u8 = 0;
    let mut v_r_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4907_ = l_Lean_IR_CtorInfo_isRef(v_info_4906_);
    crate::leanh::lean_dec_ref(v_info_4906_);
    v_r_4908_ = crate::leanh::lean_box((v_res_4907_) as usize);
    return v_r_4908_;
}
pub unsafe fn l_Lean_IR_CtorInfo_isScalar(mut v_info_4909_: *mut crate::leanh::LeanObject) -> u8 {
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
    mut v_info_4913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4914_: u8 = 0;
    let mut v_r_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4914_ = l_Lean_IR_CtorInfo_isScalar(v_info_4913_);
    crate::leanh::lean_dec_ref(v_info_4913_);
    v_r_4915_ = crate::leanh::lean_box((v_res_4914_) as usize);
    return v_r_4915_;
}
pub unsafe fn l_Lean_IR_CtorInfo_type(
    mut v_info_4916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4917_: u8 = 0;
    v___x_4917_ = l_Lean_IR_CtorInfo_isRef(v_info_4916_);
    if v___x_4917_ == 0 {
        let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4918_ = crate::leanh::lean_box(12);
        return v___x_4918_;
    } else {
        let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4919_ = crate::leanh::lean_box(7);
        return v___x_4919_;
    }
}
pub unsafe fn l_Lean_IR_CtorInfo_type___boxed(
    mut v_info_4920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4921_ = l_Lean_IR_CtorInfo_type(v_info_4920_);
    crate::leanh::lean_dec_ref(v_info_4920_);
    return v_res_4921_;
}
pub unsafe fn l_Lean_IR_Expr_ctorIdx(
    mut v_x_4922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4922_) {
        0 => {
            let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4923_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4923_;
        }
        1 => {
            let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4924_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4924_;
        }
        2 => {
            let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4925_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4925_;
        }
        3 => {
            let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4926_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_4926_;
        }
        4 => {
            let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4927_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_4927_;
        }
        5 => {
            let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4928_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_4928_;
        }
        6 => {
            let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4929_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_4929_;
        }
        7 => {
            let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4930_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_4930_;
        }
        8 => {
            let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4931_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_4931_;
        }
        9 => {
            let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4932_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_4932_;
        }
        10 => {
            let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4933_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_4933_;
        }
        11 => {
            let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4934_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_4934_;
        }
        _ => {
            let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4935_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_4935_;
        }
    }
}
pub unsafe fn l_Lean_IR_Expr_ctorIdx___boxed(
    mut v_x_4936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4937_ = l_Lean_IR_Expr_ctorIdx(v_x_4936_);
    crate::leanh::lean_dec_ref(v_x_4936_);
    return v_res_4937_;
}
pub unsafe fn l_Lean_IR_Expr_ctorElim___redArg(
    mut v_t_4938_: *mut crate::leanh::LeanObject,
    mut v_k_4939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_4938_) {
        0 => {
            let mut v_i_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ys_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_4940_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc_ref(v_i_4940_);
            v_ys_4941_ = crate::leanh::lean_ctor_get(v_t_4938_, 1);
            crate::leanh::lean_inc_ref(v_ys_4941_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 2);
            v___x_4942_ = crate::leanh::lean_apply_2(v_k_4939_, v_i_4940_, v_ys_4941_);
            return v___x_4942_;
        }
        2 => {
            let mut v_x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_updtHeader_4945_: u8 = 0;
            let mut v_ys_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_4943_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_x_4943_);
            v_i_4944_ = crate::leanh::lean_ctor_get(v_t_4938_, 1);
            crate::leanh::lean_inc_ref(v_i_4944_);
            v_updtHeader_4945_ = crate::leanh::lean_ctor_get_uint8(
                v_t_4938_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_ys_4946_ = crate::leanh::lean_ctor_get(v_t_4938_, 2);
            crate::leanh::lean_inc_ref(v_ys_4946_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 3);
            v___x_4947_ = crate::leanh::lean_box((v_updtHeader_4945_) as usize);
            v___x_4948_ = crate::leanh::lean_apply_4(
                v_k_4939_,
                v_x_4943_,
                v_i_4944_,
                v___x_4947_,
                v_ys_4946_,
            );
            return v___x_4948_;
        }
        5 => {
            let mut v_n_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_offset_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_4949_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_n_4949_);
            v_offset_4950_ = crate::leanh::lean_ctor_get(v_t_4938_, 1);
            crate::leanh::lean_inc(v_offset_4950_);
            v_x_4951_ = crate::leanh::lean_ctor_get(v_t_4938_, 2);
            crate::leanh::lean_inc(v_x_4951_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 3);
            v___x_4952_ =
                crate::leanh::lean_apply_3(v_k_4939_, v_n_4949_, v_offset_4950_, v_x_4951_);
            return v___x_4952_;
        }
        6 => {
            let mut v_c_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ys_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_4953_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_c_4953_);
            v_ys_4954_ = crate::leanh::lean_ctor_get(v_t_4938_, 1);
            crate::leanh::lean_inc_ref(v_ys_4954_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 2);
            v___x_4955_ = crate::leanh::lean_apply_2(v_k_4939_, v_c_4953_, v_ys_4954_);
            return v___x_4955_;
        }
        7 => {
            let mut v_c_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ys_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_c_4956_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_c_4956_);
            v_ys_4957_ = crate::leanh::lean_ctor_get(v_t_4938_, 1);
            crate::leanh::lean_inc_ref(v_ys_4957_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 2);
            v___x_4958_ = crate::leanh::lean_apply_2(v_k_4939_, v_c_4956_, v_ys_4957_);
            return v___x_4958_;
        }
        8 => {
            let mut v_x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ys_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_4959_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_x_4959_);
            v_ys_4960_ = crate::leanh::lean_ctor_get(v_t_4938_, 1);
            crate::leanh::lean_inc_ref(v_ys_4960_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 2);
            v___x_4961_ = crate::leanh::lean_apply_2(v_k_4939_, v_x_4959_, v_ys_4960_);
            return v___x_4961_;
        }
        10 => {
            let mut v_x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_4962_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_x_4962_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 1);
            v___x_4963_ = crate::leanh::lean_apply_1(v_k_4939_, v_x_4962_);
            return v___x_4963_;
        }
        11 => {
            let mut v_v_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_4964_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc_ref(v_v_4964_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 1);
            v___x_4965_ = crate::leanh::lean_apply_1(v_k_4939_, v_v_4964_);
            return v___x_4965_;
        }
        12 => {
            let mut v_x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_4966_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_x_4966_);
            crate::leanh::lean_dec_ref_known(v_t_4938_, 1);
            v___x_4967_ = crate::leanh::lean_apply_1(v_k_4939_, v_x_4966_);
            return v___x_4967_;
        }
        _ => {
            let mut v_n_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_4968_ = crate::leanh::lean_ctor_get(v_t_4938_, 0);
            crate::leanh::lean_inc(v_n_4968_);
            v_x_4969_ = crate::leanh::lean_ctor_get(v_t_4938_, 1);
            crate::leanh::lean_inc(v_x_4969_);
            crate::leanh::lean_dec_ref(v_t_4938_);
            v___x_4970_ = crate::leanh::lean_apply_2(v_k_4939_, v_n_4968_, v_x_4969_);
            return v___x_4970_;
        }
    }
}
pub unsafe fn l_Lean_IR_Expr_ctorElim(
    mut v_motive_4971_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4972_: *mut crate::leanh::LeanObject,
    mut v_t_4973_: *mut crate::leanh::LeanObject,
    mut v_h_4974_: *mut crate::leanh::LeanObject,
    mut v_k_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4976_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4973_, v_k_4975_);
    return v___x_4976_;
}
pub unsafe fn l_Lean_IR_Expr_ctorElim___boxed(
    mut v_motive_4977_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4978_: *mut crate::leanh::LeanObject,
    mut v_t_4979_: *mut crate::leanh::LeanObject,
    mut v_h_4980_: *mut crate::leanh::LeanObject,
    mut v_k_4981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Lean_IR_Expr_ctorElim(
        v_motive_4977_,
        v_ctorIdx_4978_,
        v_t_4979_,
        v_h_4980_,
        v_k_4981_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4978_);
    return v_res_4982_;
}
pub unsafe fn l_Lean_IR_Expr_ctor_elim___redArg(
    mut v_t_4983_: *mut crate::leanh::LeanObject,
    mut v_ctor_4984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4985_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4983_, v_ctor_4984_);
    return v___x_4985_;
}
pub unsafe fn l_Lean_IR_Expr_ctor_elim(
    mut v_motive_4986_: *mut crate::leanh::LeanObject,
    mut v_t_4987_: *mut crate::leanh::LeanObject,
    mut v_h_4988_: *mut crate::leanh::LeanObject,
    mut v_ctor_4989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4990_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4987_, v_ctor_4989_);
    return v___x_4990_;
}
pub unsafe fn l_Lean_IR_Expr_reset_elim___redArg(
    mut v_t_4991_: *mut crate::leanh::LeanObject,
    mut v_reset_4992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4993_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4991_, v_reset_4992_);
    return v___x_4993_;
}
pub unsafe fn l_Lean_IR_Expr_reset_elim(
    mut v_motive_4994_: *mut crate::leanh::LeanObject,
    mut v_t_4995_: *mut crate::leanh::LeanObject,
    mut v_h_4996_: *mut crate::leanh::LeanObject,
    mut v_reset_4997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4998_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4995_, v_reset_4997_);
    return v___x_4998_;
}
pub unsafe fn l_Lean_IR_Expr_reuse_elim___redArg(
    mut v_t_4999_: *mut crate::leanh::LeanObject,
    mut v_reuse_5000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5001_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_4999_, v_reuse_5000_);
    return v___x_5001_;
}
pub unsafe fn l_Lean_IR_Expr_reuse_elim(
    mut v_motive_5002_: *mut crate::leanh::LeanObject,
    mut v_t_5003_: *mut crate::leanh::LeanObject,
    mut v_h_5004_: *mut crate::leanh::LeanObject,
    mut v_reuse_5005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5006_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5003_, v_reuse_5005_);
    return v___x_5006_;
}
pub unsafe fn l_Lean_IR_Expr_proj_elim___redArg(
    mut v_t_5007_: *mut crate::leanh::LeanObject,
    mut v_proj_5008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5009_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5007_, v_proj_5008_);
    return v___x_5009_;
}
pub unsafe fn l_Lean_IR_Expr_proj_elim(
    mut v_motive_5010_: *mut crate::leanh::LeanObject,
    mut v_t_5011_: *mut crate::leanh::LeanObject,
    mut v_h_5012_: *mut crate::leanh::LeanObject,
    mut v_proj_5013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5014_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5011_, v_proj_5013_);
    return v___x_5014_;
}
pub unsafe fn l_Lean_IR_Expr_uproj_elim___redArg(
    mut v_t_5015_: *mut crate::leanh::LeanObject,
    mut v_uproj_5016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5017_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5015_, v_uproj_5016_);
    return v___x_5017_;
}
pub unsafe fn l_Lean_IR_Expr_uproj_elim(
    mut v_motive_5018_: *mut crate::leanh::LeanObject,
    mut v_t_5019_: *mut crate::leanh::LeanObject,
    mut v_h_5020_: *mut crate::leanh::LeanObject,
    mut v_uproj_5021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5022_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5019_, v_uproj_5021_);
    return v___x_5022_;
}
pub unsafe fn l_Lean_IR_Expr_sproj_elim___redArg(
    mut v_t_5023_: *mut crate::leanh::LeanObject,
    mut v_sproj_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5023_, v_sproj_5024_);
    return v___x_5025_;
}
pub unsafe fn l_Lean_IR_Expr_sproj_elim(
    mut v_motive_5026_: *mut crate::leanh::LeanObject,
    mut v_t_5027_: *mut crate::leanh::LeanObject,
    mut v_h_5028_: *mut crate::leanh::LeanObject,
    mut v_sproj_5029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5030_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5027_, v_sproj_5029_);
    return v___x_5030_;
}
pub unsafe fn l_Lean_IR_Expr_fap_elim___redArg(
    mut v_t_5031_: *mut crate::leanh::LeanObject,
    mut v_fap_5032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5033_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5031_, v_fap_5032_);
    return v___x_5033_;
}
pub unsafe fn l_Lean_IR_Expr_fap_elim(
    mut v_motive_5034_: *mut crate::leanh::LeanObject,
    mut v_t_5035_: *mut crate::leanh::LeanObject,
    mut v_h_5036_: *mut crate::leanh::LeanObject,
    mut v_fap_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5038_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5035_, v_fap_5037_);
    return v___x_5038_;
}
pub unsafe fn l_Lean_IR_Expr_pap_elim___redArg(
    mut v_t_5039_: *mut crate::leanh::LeanObject,
    mut v_pap_5040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5041_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5039_, v_pap_5040_);
    return v___x_5041_;
}
pub unsafe fn l_Lean_IR_Expr_pap_elim(
    mut v_motive_5042_: *mut crate::leanh::LeanObject,
    mut v_t_5043_: *mut crate::leanh::LeanObject,
    mut v_h_5044_: *mut crate::leanh::LeanObject,
    mut v_pap_5045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5046_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5043_, v_pap_5045_);
    return v___x_5046_;
}
pub unsafe fn l_Lean_IR_Expr_ap_elim___redArg(
    mut v_t_5047_: *mut crate::leanh::LeanObject,
    mut v_ap_5048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5049_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5047_, v_ap_5048_);
    return v___x_5049_;
}
pub unsafe fn l_Lean_IR_Expr_ap_elim(
    mut v_motive_5050_: *mut crate::leanh::LeanObject,
    mut v_t_5051_: *mut crate::leanh::LeanObject,
    mut v_h_5052_: *mut crate::leanh::LeanObject,
    mut v_ap_5053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5054_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5051_, v_ap_5053_);
    return v___x_5054_;
}
pub unsafe fn l_Lean_IR_Expr_box_elim___redArg(
    mut v_t_5055_: *mut crate::leanh::LeanObject,
    mut v_box_5056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5057_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5055_, v_box_5056_);
    return v___x_5057_;
}
pub unsafe fn l_Lean_IR_Expr_box_elim(
    mut v_motive_5058_: *mut crate::leanh::LeanObject,
    mut v_t_5059_: *mut crate::leanh::LeanObject,
    mut v_h_5060_: *mut crate::leanh::LeanObject,
    mut v_box_5061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5062_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5059_, v_box_5061_);
    return v___x_5062_;
}
pub unsafe fn l_Lean_IR_Expr_unbox_elim___redArg(
    mut v_t_5063_: *mut crate::leanh::LeanObject,
    mut v_unbox_5064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5065_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5063_, v_unbox_5064_);
    return v___x_5065_;
}
pub unsafe fn l_Lean_IR_Expr_unbox_elim(
    mut v_motive_5066_: *mut crate::leanh::LeanObject,
    mut v_t_5067_: *mut crate::leanh::LeanObject,
    mut v_h_5068_: *mut crate::leanh::LeanObject,
    mut v_unbox_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5070_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5067_, v_unbox_5069_);
    return v___x_5070_;
}
pub unsafe fn l_Lean_IR_Expr_lit_elim___redArg(
    mut v_t_5071_: *mut crate::leanh::LeanObject,
    mut v_lit_5072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5073_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5071_, v_lit_5072_);
    return v___x_5073_;
}
pub unsafe fn l_Lean_IR_Expr_lit_elim(
    mut v_motive_5074_: *mut crate::leanh::LeanObject,
    mut v_t_5075_: *mut crate::leanh::LeanObject,
    mut v_h_5076_: *mut crate::leanh::LeanObject,
    mut v_lit_5077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5078_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5075_, v_lit_5077_);
    return v___x_5078_;
}
pub unsafe fn l_Lean_IR_Expr_isShared_elim___redArg(
    mut v_t_5079_: *mut crate::leanh::LeanObject,
    mut v_isShared_5080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5081_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5079_, v_isShared_5080_);
    return v___x_5081_;
}
pub unsafe fn l_Lean_IR_Expr_isShared_elim(
    mut v_motive_5082_: *mut crate::leanh::LeanObject,
    mut v_t_5083_: *mut crate::leanh::LeanObject,
    mut v_h_5084_: *mut crate::leanh::LeanObject,
    mut v_isShared_5085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5086_ = l_Lean_IR_Expr_ctorElim___redArg(v_t_5083_, v_isShared_5085_);
    return v___x_5086_;
}
pub unsafe fn _init_l_Lean_IR_instReprParam_repr___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5109_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_5110_ = lean_nat_to_int(v___x_5109_);
    return v___x_5110_;
}
pub unsafe fn _init_l_Lean_IR_instReprParam_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5114_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_5115_ = lean_nat_to_int(v___x_5114_);
    return v___x_5115_;
}
pub unsafe fn _init_l_Lean_IR_instReprParam_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5119_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_5120_ = lean_nat_to_int(v___x_5119_);
    return v___x_5120_;
}
pub unsafe fn l_Lean_IR_instReprParam_repr___redArg(
    mut v_x_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_5123_: u8 = 0;
    let mut v_ty_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: u8 = 0;
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5122_ = crate::leanh::lean_ctor_get(v_x_5121_, 0);
    crate::leanh::lean_inc(v_x_5122_);
    v_borrow_5123_ = crate::leanh::lean_ctor_get_uint8(
        v_x_5121_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v_ty_5124_ = crate::leanh::lean_ctor_get(v_x_5121_, 1);
    crate::leanh::lean_inc(v_ty_5124_);
    crate::leanh::lean_dec_ref(v_x_5121_);
    v___x_5125_ = l_Lean_IR_instReprVarId_repr___redArg___closed__5;
    v___x_5126_ = l_Lean_IR_instReprParam_repr___redArg___closed__3;
    v___x_5127_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__4_once),
        _init_l_Lean_IR_instReprParam_repr___redArg___closed__4,
    );
    v___x_5128_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5129_ = l_Lean_IR_instReprVarId_repr___redArg(v_x_5122_);
    v___x_5130_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5130_, 0, v___x_5127_);
    crate::leanh::lean_ctor_set(v___x_5130_, 1, v___x_5129_);
    v___x_5131_ = 0;
    v___x_5132_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5132_, 0, v___x_5130_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5132_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    v___x_5133_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5133_, 0, v___x_5126_);
    crate::leanh::lean_ctor_set(v___x_5133_, 1, v___x_5132_);
    v___x_5134_ = l_Array_repr___at___00Lean_IR_instReprIRType_repr_spec__1___closed__2;
    v___x_5135_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5135_, 0, v___x_5133_);
    crate::leanh::lean_ctor_set(v___x_5135_, 1, v___x_5134_);
    v___x_5136_ = crate::leanh::lean_box(1);
    v___x_5137_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5135_);
    crate::leanh::lean_ctor_set(v___x_5137_, 1, v___x_5136_);
    v___x_5138_ = l_Lean_IR_instReprParam_repr___redArg___closed__6;
    v___x_5139_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5139_, 0, v___x_5137_);
    crate::leanh::lean_ctor_set(v___x_5139_, 1, v___x_5138_);
    v___x_5140_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5140_, 0, v___x_5139_);
    crate::leanh::lean_ctor_set(v___x_5140_, 1, v___x_5125_);
    v___x_5141_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__7_once),
        _init_l_Lean_IR_instReprParam_repr___redArg___closed__7,
    );
    v___x_5142_ = l_Bool_repr___redArg(v_borrow_5123_);
    v___x_5143_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5143_, 0, v___x_5141_);
    crate::leanh::lean_ctor_set(v___x_5143_, 1, v___x_5142_);
    v___x_5144_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5144_, 0, v___x_5143_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5144_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    v___x_5145_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5145_, 0, v___x_5140_);
    crate::leanh::lean_ctor_set(v___x_5145_, 1, v___x_5144_);
    v___x_5146_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5146_, 0, v___x_5145_);
    crate::leanh::lean_ctor_set(v___x_5146_, 1, v___x_5134_);
    v___x_5147_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5147_, 0, v___x_5146_);
    crate::leanh::lean_ctor_set(v___x_5147_, 1, v___x_5136_);
    v___x_5148_ = l_Lean_IR_instReprParam_repr___redArg___closed__9;
    v___x_5149_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5149_, 0, v___x_5147_);
    crate::leanh::lean_ctor_set(v___x_5149_, 1, v___x_5148_);
    v___x_5150_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5150_, 0, v___x_5149_);
    crate::leanh::lean_ctor_set(v___x_5150_, 1, v___x_5125_);
    v___x_5151_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprParam_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprParam_repr___redArg___closed__10,
    );
    v___x_5152_ = l_Lean_IR_instReprIRType_repr(v_ty_5124_, v___x_5128_);
    v___x_5153_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5153_, 0, v___x_5151_);
    crate::leanh::lean_ctor_set(v___x_5153_, 1, v___x_5152_);
    v___x_5154_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5154_, 0, v___x_5153_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5154_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    v___x_5155_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5155_, 0, v___x_5150_);
    crate::leanh::lean_ctor_set(v___x_5155_, 1, v___x_5154_);
    v___x_5156_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_IR_instReprVarId_repr___redArg___closed__10_once),
        _init_l_Lean_IR_instReprVarId_repr___redArg___closed__10,
    );
    v___x_5157_ = l_Lean_IR_instReprVarId_repr___redArg___closed__11;
    v___x_5158_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5158_, 0, v___x_5157_);
    crate::leanh::lean_ctor_set(v___x_5158_, 1, v___x_5155_);
    v___x_5159_ = l_Lean_IR_instReprVarId_repr___redArg___closed__12;
    v___x_5160_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5160_, 0, v___x_5158_);
    crate::leanh::lean_ctor_set(v___x_5160_, 1, v___x_5159_);
    v___x_5161_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5161_, 0, v___x_5156_);
    crate::leanh::lean_ctor_set(v___x_5161_, 1, v___x_5160_);
    v___x_5162_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_5162_, 0, v___x_5161_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5162_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_5131_,
    );
    return v___x_5162_;
}
pub unsafe fn l_Lean_IR_instReprParam_repr(
    mut v_x_5163_: *mut crate::leanh::LeanObject,
    mut v_prec_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5165_ = l_Lean_IR_instReprParam_repr___redArg(v_x_5163_);
    return v___x_5165_;
}
pub unsafe fn l_Lean_IR_instReprParam_repr___boxed(
    mut v_x_5166_: *mut crate::leanh::LeanObject,
    mut v_prec_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5168_ = l_Lean_IR_instReprParam_repr(v_x_5166_, v_prec_5167_);
    crate::leanh::lean_dec(v_prec_5167_);
    return v_res_5168_;
}
pub unsafe fn l_Lean_IR_Alt_ctorIdx(
    mut v_x_5171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5171_) == 0 {
        let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5172_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_5172_;
    } else {
        let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5173_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_5173_;
    }
}
pub unsafe fn l_Lean_IR_Alt_ctorIdx___boxed(
    mut v_x_5174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5175_ = l_Lean_IR_Alt_ctorIdx(v_x_5174_);
    crate::leanh::lean_dec_ref(v_x_5174_);
    return v_res_5175_;
}
pub unsafe fn l_Lean_IR_Alt_ctorElim___redArg(
    mut v_t_5176_: *mut crate::leanh::LeanObject,
    mut v_k_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5176_) == 0 {
        let mut v_info_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_b_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_info_5178_ = crate::leanh::lean_ctor_get(v_t_5176_, 0);
        crate::leanh::lean_inc_ref(v_info_5178_);
        v_b_5179_ = crate::leanh::lean_ctor_get(v_t_5176_, 1);
        crate::leanh::lean_inc(v_b_5179_);
        crate::leanh::lean_dec_ref_known(v_t_5176_, 2);
        v___x_5180_ = crate::leanh::lean_apply_2(v_k_5177_, v_info_5178_, v_b_5179_);
        return v___x_5180_;
    } else {
        let mut v_b_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_b_5181_ = crate::leanh::lean_ctor_get(v_t_5176_, 0);
        crate::leanh::lean_inc(v_b_5181_);
        crate::leanh::lean_dec_ref_known(v_t_5176_, 1);
        v___x_5182_ = crate::leanh::lean_apply_1(v_k_5177_, v_b_5181_);
        return v___x_5182_;
    }
}
pub unsafe fn l_Lean_IR_Alt_ctorElim(
    mut v_motive__1_5183_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5184_: *mut crate::leanh::LeanObject,
    mut v_t_5185_: *mut crate::leanh::LeanObject,
    mut v_h_5186_: *mut crate::leanh::LeanObject,
    mut v_k_5187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5188_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5185_, v_k_5187_);
    return v___x_5188_;
}
pub unsafe fn l_Lean_IR_Alt_ctorElim___boxed(
    mut v_motive__1_5189_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5190_: *mut crate::leanh::LeanObject,
    mut v_t_5191_: *mut crate::leanh::LeanObject,
    mut v_h_5192_: *mut crate::leanh::LeanObject,
    mut v_k_5193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5194_ = l_Lean_IR_Alt_ctorElim(
        v_motive__1_5189_,
        v_ctorIdx_5190_,
        v_t_5191_,
        v_h_5192_,
        v_k_5193_,
    );
    crate::leanh::lean_dec(v_ctorIdx_5190_);
    return v_res_5194_;
}
pub unsafe fn l_Lean_IR_Alt_ctor_elim___redArg(
    mut v_t_5195_: *mut crate::leanh::LeanObject,
    mut v_ctor_5196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5197_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5195_, v_ctor_5196_);
    return v___x_5197_;
}
pub unsafe fn l_Lean_IR_Alt_ctor_elim(
    mut v_motive__1_5198_: *mut crate::leanh::LeanObject,
    mut v_t_5199_: *mut crate::leanh::LeanObject,
    mut v_h_5200_: *mut crate::leanh::LeanObject,
    mut v_ctor_5201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5202_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5199_, v_ctor_5201_);
    return v___x_5202_;
}
pub unsafe fn l_Lean_IR_Alt_default_elim___redArg(
    mut v_t_5203_: *mut crate::leanh::LeanObject,
    mut v_default_5204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5205_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5203_, v_default_5204_);
    return v___x_5205_;
}
pub unsafe fn l_Lean_IR_Alt_default_elim(
    mut v_motive__1_5206_: *mut crate::leanh::LeanObject,
    mut v_t_5207_: *mut crate::leanh::LeanObject,
    mut v_h_5208_: *mut crate::leanh::LeanObject,
    mut v_default_5209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5210_ = l_Lean_IR_Alt_ctorElim___redArg(v_t_5207_, v_default_5209_);
    return v___x_5210_;
}
pub unsafe fn l_Lean_IR_FnBody_ctorIdx(
    mut v_x_5211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_5211_) {
        0 => {
            let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5212_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_5212_;
        }
        1 => {
            let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5213_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_5213_;
        }
        2 => {
            let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5214_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_5214_;
        }
        3 => {
            let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5215_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_5215_;
        }
        4 => {
            let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5216_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_5216_;
        }
        5 => {
            let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5217_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_5217_;
        }
        6 => {
            let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5218_ = crate::leanh::lean_unsigned_to_nat(6);
            return v___x_5218_;
        }
        7 => {
            let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5219_ = crate::leanh::lean_unsigned_to_nat(7);
            return v___x_5219_;
        }
        8 => {
            let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5220_ = crate::leanh::lean_unsigned_to_nat(8);
            return v___x_5220_;
        }
        9 => {
            let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5221_ = crate::leanh::lean_unsigned_to_nat(9);
            return v___x_5221_;
        }
        10 => {
            let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5222_ = crate::leanh::lean_unsigned_to_nat(10);
            return v___x_5222_;
        }
        11 => {
            let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5223_ = crate::leanh::lean_unsigned_to_nat(11);
            return v___x_5223_;
        }
        _ => {
            let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5224_ = crate::leanh::lean_unsigned_to_nat(12);
            return v___x_5224_;
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_ctorIdx___boxed(
    mut v_x_5225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5226_ = l_Lean_IR_FnBody_ctorIdx(v_x_5225_);
    crate::leanh::lean_dec(v_x_5225_);
    return v_res_5226_;
}
pub unsafe fn l_Lean_IR_FnBody_ctorElim___redArg(
    mut v_t_5227_: *mut crate::leanh::LeanObject,
    mut v_k_5228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_5227_) {
        0 => {
            let mut v_x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ty_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5229_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5229_);
            v_ty_5230_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_ty_5230_);
            v_e_5231_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc_ref(v_e_5231_);
            v_b_5232_ = crate::leanh::lean_ctor_get(v_t_5227_, 3);
            crate::leanh::lean_inc(v_b_5232_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 4);
            v___x_5233_ =
                crate::leanh::lean_apply_4(v_k_5228_, v_x_5229_, v_ty_5230_, v_e_5231_, v_b_5232_);
            return v___x_5233_;
        }
        1 => {
            let mut v_j_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_xs_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_v_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_j_5234_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_j_5234_);
            v_xs_5235_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc_ref(v_xs_5235_);
            v_v_5236_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc(v_v_5236_);
            v_b_5237_ = crate::leanh::lean_ctor_get(v_t_5227_, 3);
            crate::leanh::lean_inc(v_b_5237_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 4);
            v___x_5238_ =
                crate::leanh::lean_apply_4(v_k_5228_, v_j_5234_, v_xs_5235_, v_v_5236_, v_b_5237_);
            return v___x_5238_;
        }
        3 => {
            let mut v_x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_cidx_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5239_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5239_);
            v_cidx_5240_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_cidx_5240_);
            v_b_5241_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc(v_b_5241_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 3);
            v___x_5242_ = crate::leanh::lean_apply_3(v_k_5228_, v_x_5239_, v_cidx_5240_, v_b_5241_);
            return v___x_5242_;
        }
        5 => {
            let mut v_x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_offset_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ty_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5243_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5243_);
            v_i_5244_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_i_5244_);
            v_offset_5245_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc(v_offset_5245_);
            v_y_5246_ = crate::leanh::lean_ctor_get(v_t_5227_, 3);
            crate::leanh::lean_inc(v_y_5246_);
            v_ty_5247_ = crate::leanh::lean_ctor_get(v_t_5227_, 4);
            crate::leanh::lean_inc(v_ty_5247_);
            v_b_5248_ = crate::leanh::lean_ctor_get(v_t_5227_, 5);
            crate::leanh::lean_inc(v_b_5248_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 6);
            v___x_5249_ = crate::leanh::lean_apply_6(
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
            let mut v_x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_5252_: u8 = 0;
            let mut v_persistent_5253_: u8 = 0;
            let mut v_b_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5250_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5250_);
            v_n_5251_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_n_5251_);
            v_c_5252_ = crate::leanh::lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_persistent_5253_ = crate::leanh::lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
            );
            v_b_5254_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc(v_b_5254_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 3);
            v___x_5255_ = crate::leanh::lean_box((v_c_5252_) as usize);
            v___x_5256_ = crate::leanh::lean_box((v_persistent_5253_) as usize);
            v___x_5257_ = crate::leanh::lean_apply_5(
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
            let mut v_x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_5260_: u8 = 0;
            let mut v_persistent_5261_: u8 = 0;
            let mut v_b_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5258_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5258_);
            v_n_5259_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_n_5259_);
            v_c_5260_ = crate::leanh::lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
            );
            v_persistent_5261_ = crate::leanh::lean_ctor_get_uint8(
                v_t_5227_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
            );
            v_b_5262_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc(v_b_5262_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 3);
            v___x_5263_ = crate::leanh::lean_box((v_c_5260_) as usize);
            v___x_5264_ = crate::leanh::lean_box((v_persistent_5261_) as usize);
            v___x_5265_ = crate::leanh::lean_apply_5(
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
            let mut v_x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5266_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5266_);
            v_b_5267_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_b_5267_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 2);
            v___x_5268_ = crate::leanh::lean_apply_2(v_k_5228_, v_x_5266_, v_b_5267_);
            return v___x_5268_;
        }
        9 => {
            let mut v_tid_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_xType_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_cs_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_tid_5269_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_tid_5269_);
            v_x_5270_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_x_5270_);
            v_xType_5271_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc(v_xType_5271_);
            v_cs_5272_ = crate::leanh::lean_ctor_get(v_t_5227_, 3);
            crate::leanh::lean_inc_ref(v_cs_5272_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 4);
            v___x_5273_ = crate::leanh::lean_apply_4(
                v_k_5228_,
                v_tid_5269_,
                v_x_5270_,
                v_xType_5271_,
                v_cs_5272_,
            );
            return v___x_5273_;
        }
        10 => {
            let mut v_x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5274_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5274_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 1);
            v___x_5275_ = crate::leanh::lean_apply_1(v_k_5228_, v_x_5274_);
            return v___x_5275_;
        }
        11 => {
            let mut v_j_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ys_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_j_5276_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_j_5276_);
            v_ys_5277_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc_ref(v_ys_5277_);
            crate::leanh::lean_dec_ref_known(v_t_5227_, 2);
            v___x_5278_ = crate::leanh::lean_apply_2(v_k_5228_, v_j_5276_, v_ys_5277_);
            return v___x_5278_;
        }
        12 => {
            return v_k_5228_;
        }
        _ => {
            let mut v_x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_y_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_x_5279_ = crate::leanh::lean_ctor_get(v_t_5227_, 0);
            crate::leanh::lean_inc(v_x_5279_);
            v_i_5280_ = crate::leanh::lean_ctor_get(v_t_5227_, 1);
            crate::leanh::lean_inc(v_i_5280_);
            v_y_5281_ = crate::leanh::lean_ctor_get(v_t_5227_, 2);
            crate::leanh::lean_inc(v_y_5281_);
            v_b_5282_ = crate::leanh::lean_ctor_get(v_t_5227_, 3);
            crate::leanh::lean_inc(v_b_5282_);
            crate::leanh::lean_dec(v_t_5227_);
            v___x_5283_ =
                crate::leanh::lean_apply_4(v_k_5228_, v_x_5279_, v_i_5280_, v_y_5281_, v_b_5282_);
            return v___x_5283_;
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_ctorElim(
    mut v_motive__2_5284_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5285_: *mut crate::leanh::LeanObject,
    mut v_t_5286_: *mut crate::leanh::LeanObject,
    mut v_h_5287_: *mut crate::leanh::LeanObject,
    mut v_k_5288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5289_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5286_, v_k_5288_);
    return v___x_5289_;
}
pub unsafe fn l_Lean_IR_FnBody_ctorElim___boxed(
    mut v_motive__2_5290_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5291_: *mut crate::leanh::LeanObject,
    mut v_t_5292_: *mut crate::leanh::LeanObject,
    mut v_h_5293_: *mut crate::leanh::LeanObject,
    mut v_k_5294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5295_ = l_Lean_IR_FnBody_ctorElim(
        v_motive__2_5290_,
        v_ctorIdx_5291_,
        v_t_5292_,
        v_h_5293_,
        v_k_5294_,
    );
    crate::leanh::lean_dec(v_ctorIdx_5291_);
    return v_res_5295_;
}
pub unsafe fn l_Lean_IR_FnBody_vdecl_elim___redArg(
    mut v_t_5296_: *mut crate::leanh::LeanObject,
    mut v_vdecl_5297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5298_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5296_, v_vdecl_5297_);
    return v___x_5298_;
}
pub unsafe fn l_Lean_IR_FnBody_vdecl_elim(
    mut v_motive__2_5299_: *mut crate::leanh::LeanObject,
    mut v_t_5300_: *mut crate::leanh::LeanObject,
    mut v_h_5301_: *mut crate::leanh::LeanObject,
    mut v_vdecl_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5303_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5300_, v_vdecl_5302_);
    return v___x_5303_;
}
pub unsafe fn l_Lean_IR_FnBody_jdecl_elim___redArg(
    mut v_t_5304_: *mut crate::leanh::LeanObject,
    mut v_jdecl_5305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5306_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5304_, v_jdecl_5305_);
    return v___x_5306_;
}
pub unsafe fn l_Lean_IR_FnBody_jdecl_elim(
    mut v_motive__2_5307_: *mut crate::leanh::LeanObject,
    mut v_t_5308_: *mut crate::leanh::LeanObject,
    mut v_h_5309_: *mut crate::leanh::LeanObject,
    mut v_jdecl_5310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5311_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5308_, v_jdecl_5310_);
    return v___x_5311_;
}
pub unsafe fn l_Lean_IR_FnBody_set_elim___redArg(
    mut v_t_5312_: *mut crate::leanh::LeanObject,
    mut v_set_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5314_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5312_, v_set_5313_);
    return v___x_5314_;
}
pub unsafe fn l_Lean_IR_FnBody_set_elim(
    mut v_motive__2_5315_: *mut crate::leanh::LeanObject,
    mut v_t_5316_: *mut crate::leanh::LeanObject,
    mut v_h_5317_: *mut crate::leanh::LeanObject,
    mut v_set_5318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5319_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5316_, v_set_5318_);
    return v___x_5319_;
}
pub unsafe fn l_Lean_IR_FnBody_setTag_elim___redArg(
    mut v_t_5320_: *mut crate::leanh::LeanObject,
    mut v_setTag_5321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5322_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5320_, v_setTag_5321_);
    return v___x_5322_;
}
pub unsafe fn l_Lean_IR_FnBody_setTag_elim(
    mut v_motive__2_5323_: *mut crate::leanh::LeanObject,
    mut v_t_5324_: *mut crate::leanh::LeanObject,
    mut v_h_5325_: *mut crate::leanh::LeanObject,
    mut v_setTag_5326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5327_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5324_, v_setTag_5326_);
    return v___x_5327_;
}
pub unsafe fn l_Lean_IR_FnBody_uset_elim___redArg(
    mut v_t_5328_: *mut crate::leanh::LeanObject,
    mut v_uset_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5330_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5328_, v_uset_5329_);
    return v___x_5330_;
}
pub unsafe fn l_Lean_IR_FnBody_uset_elim(
    mut v_motive__2_5331_: *mut crate::leanh::LeanObject,
    mut v_t_5332_: *mut crate::leanh::LeanObject,
    mut v_h_5333_: *mut crate::leanh::LeanObject,
    mut v_uset_5334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5335_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5332_, v_uset_5334_);
    return v___x_5335_;
}
pub unsafe fn l_Lean_IR_FnBody_sset_elim___redArg(
    mut v_t_5336_: *mut crate::leanh::LeanObject,
    mut v_sset_5337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5338_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5336_, v_sset_5337_);
    return v___x_5338_;
}
pub unsafe fn l_Lean_IR_FnBody_sset_elim(
    mut v_motive__2_5339_: *mut crate::leanh::LeanObject,
    mut v_t_5340_: *mut crate::leanh::LeanObject,
    mut v_h_5341_: *mut crate::leanh::LeanObject,
    mut v_sset_5342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5343_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5340_, v_sset_5342_);
    return v___x_5343_;
}
pub unsafe fn l_Lean_IR_FnBody_inc_elim___redArg(
    mut v_t_5344_: *mut crate::leanh::LeanObject,
    mut v_inc_5345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5346_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5344_, v_inc_5345_);
    return v___x_5346_;
}
pub unsafe fn l_Lean_IR_FnBody_inc_elim(
    mut v_motive__2_5347_: *mut crate::leanh::LeanObject,
    mut v_t_5348_: *mut crate::leanh::LeanObject,
    mut v_h_5349_: *mut crate::leanh::LeanObject,
    mut v_inc_5350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5351_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5348_, v_inc_5350_);
    return v___x_5351_;
}
pub unsafe fn l_Lean_IR_FnBody_dec_elim___redArg(
    mut v_t_5352_: *mut crate::leanh::LeanObject,
    mut v_dec_5353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5354_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5352_, v_dec_5353_);
    return v___x_5354_;
}
pub unsafe fn l_Lean_IR_FnBody_dec_elim(
    mut v_motive__2_5355_: *mut crate::leanh::LeanObject,
    mut v_t_5356_: *mut crate::leanh::LeanObject,
    mut v_h_5357_: *mut crate::leanh::LeanObject,
    mut v_dec_5358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5359_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5356_, v_dec_5358_);
    return v___x_5359_;
}
pub unsafe fn l_Lean_IR_FnBody_del_elim___redArg(
    mut v_t_5360_: *mut crate::leanh::LeanObject,
    mut v_del_5361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5362_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5360_, v_del_5361_);
    return v___x_5362_;
}
pub unsafe fn l_Lean_IR_FnBody_del_elim(
    mut v_motive__2_5363_: *mut crate::leanh::LeanObject,
    mut v_t_5364_: *mut crate::leanh::LeanObject,
    mut v_h_5365_: *mut crate::leanh::LeanObject,
    mut v_del_5366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5367_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5364_, v_del_5366_);
    return v___x_5367_;
}
pub unsafe fn l_Lean_IR_FnBody_case_elim___redArg(
    mut v_t_5368_: *mut crate::leanh::LeanObject,
    mut v_case_5369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5370_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5368_, v_case_5369_);
    return v___x_5370_;
}
pub unsafe fn l_Lean_IR_FnBody_case_elim(
    mut v_motive__2_5371_: *mut crate::leanh::LeanObject,
    mut v_t_5372_: *mut crate::leanh::LeanObject,
    mut v_h_5373_: *mut crate::leanh::LeanObject,
    mut v_case_5374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5375_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5372_, v_case_5374_);
    return v___x_5375_;
}
pub unsafe fn l_Lean_IR_FnBody_ret_elim___redArg(
    mut v_t_5376_: *mut crate::leanh::LeanObject,
    mut v_ret_5377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5378_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5376_, v_ret_5377_);
    return v___x_5378_;
}
pub unsafe fn l_Lean_IR_FnBody_ret_elim(
    mut v_motive__2_5379_: *mut crate::leanh::LeanObject,
    mut v_t_5380_: *mut crate::leanh::LeanObject,
    mut v_h_5381_: *mut crate::leanh::LeanObject,
    mut v_ret_5382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5383_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5380_, v_ret_5382_);
    return v___x_5383_;
}
pub unsafe fn l_Lean_IR_FnBody_jmp_elim___redArg(
    mut v_t_5384_: *mut crate::leanh::LeanObject,
    mut v_jmp_5385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5386_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5384_, v_jmp_5385_);
    return v___x_5386_;
}
pub unsafe fn l_Lean_IR_FnBody_jmp_elim(
    mut v_motive__2_5387_: *mut crate::leanh::LeanObject,
    mut v_t_5388_: *mut crate::leanh::LeanObject,
    mut v_h_5389_: *mut crate::leanh::LeanObject,
    mut v_jmp_5390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5391_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5388_, v_jmp_5390_);
    return v___x_5391_;
}
pub unsafe fn l_Lean_IR_FnBody_unreachable_elim___redArg(
    mut v_t_5392_: *mut crate::leanh::LeanObject,
    mut v_unreachable_5393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5394_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5392_, v_unreachable_5393_);
    return v___x_5394_;
}
pub unsafe fn l_Lean_IR_FnBody_unreachable_elim(
    mut v_motive__2_5395_: *mut crate::leanh::LeanObject,
    mut v_t_5396_: *mut crate::leanh::LeanObject,
    mut v_h_5397_: *mut crate::leanh::LeanObject,
    mut v_unreachable_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_Lean_IR_FnBody_ctorElim___redArg(v_t_5396_, v_unreachable_5398_);
    return v___x_5399_;
}
pub unsafe fn _init_l_Lean_IR_FnBody_nil() -> *mut crate::leanh::LeanObject {
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5414_ = crate::leanh::lean_box(12);
    return v___x_5414_;
}
pub unsafe fn l_Lean_IR_FnBody_isTerminal(mut v_x_5415_: *mut crate::leanh::LeanObject) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_5415_) {
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
    mut v_x_5421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5422_: u8 = 0;
    let mut v_r_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5422_ = l_Lean_IR_FnBody_isTerminal(v_x_5421_);
    crate::leanh::lean_dec(v_x_5421_);
    v_r_5423_ = crate::leanh::lean_box((v_res_5422_) as usize);
    return v_r_5423_;
}
pub unsafe fn l_Lean_IR_FnBody_body(
    mut v_x_5424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_5424_) {
        0 => {
            let mut v_b_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5425_ = crate::leanh::lean_ctor_get(v_x_5424_, 3);
            crate::leanh::lean_inc(v_b_5425_);
            return v_b_5425_;
        }
        1 => {
            let mut v_b_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5426_ = crate::leanh::lean_ctor_get(v_x_5424_, 3);
            crate::leanh::lean_inc(v_b_5426_);
            return v_b_5426_;
        }
        2 => {
            let mut v_b_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5427_ = crate::leanh::lean_ctor_get(v_x_5424_, 3);
            crate::leanh::lean_inc(v_b_5427_);
            return v_b_5427_;
        }
        4 => {
            let mut v_b_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5428_ = crate::leanh::lean_ctor_get(v_x_5424_, 3);
            crate::leanh::lean_inc(v_b_5428_);
            return v_b_5428_;
        }
        5 => {
            let mut v_b_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5429_ = crate::leanh::lean_ctor_get(v_x_5424_, 5);
            crate::leanh::lean_inc(v_b_5429_);
            return v_b_5429_;
        }
        3 => {
            let mut v_b_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5430_ = crate::leanh::lean_ctor_get(v_x_5424_, 2);
            crate::leanh::lean_inc(v_b_5430_);
            return v_b_5430_;
        }
        6 => {
            let mut v_b_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5431_ = crate::leanh::lean_ctor_get(v_x_5424_, 2);
            crate::leanh::lean_inc(v_b_5431_);
            return v_b_5431_;
        }
        7 => {
            let mut v_b_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5432_ = crate::leanh::lean_ctor_get(v_x_5424_, 2);
            crate::leanh::lean_inc(v_b_5432_);
            return v_b_5432_;
        }
        8 => {
            let mut v_b_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_5433_ = crate::leanh::lean_ctor_get(v_x_5424_, 1);
            crate::leanh::lean_inc(v_b_5433_);
            return v_b_5433_;
        }
        _ => {
            crate::leanh::lean_inc(v_x_5424_);
            return v_x_5424_;
        }
    }
}
pub unsafe fn l_Lean_IR_FnBody_body___boxed(
    mut v_x_5434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5435_ = l_Lean_IR_FnBody_body(v_x_5434_);
    crate::leanh::lean_dec(v_x_5434_);
    return v_res_5435_;
}
pub unsafe fn l_Lean_IR_FnBody_setBody(
    mut v_x_5436_: *mut crate::leanh::LeanObject,
    mut v_x_5437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5447_: u8 = 0;
    let mut v_unused_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_unused_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5465_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v_unused_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5476_: u8 = 0;
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5480_: u8 = 0;
    let mut v_unused_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5489_: u8 = 0;
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut v_unused_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5499_: u8 = 0;
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5503_: u8 = 0;
    let mut v_unused_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5507_: u8 = 0;
    let mut v_persistent_5508_: u8 = 0;
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5511_: u8 = 0;
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5515_: u8 = 0;
    let mut v_unused_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5519_: u8 = 0;
    let mut v_persistent_5520_: u8 = 0;
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5523_: u8 = 0;
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5527_: u8 = 0;
    let mut v_unused_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_unused_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_5436_) {
                0 => {
                    v_x_5438_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_ty_5439_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_e_5440_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5447_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5447_ == 0 {
                        v_unused_5448_ = crate::leanh::lean_ctor_get(v_x_5436_, 3);
                        crate::leanh::lean_dec(v_unused_5448_);
                        v___x_5442_ = v_x_5436_;
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_e_5440_);
                        crate::leanh::lean_inc(v_ty_5439_);
                        crate::leanh::lean_inc(v_x_5438_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5442_ = crate::leanh::lean_box(0);
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_j_5449_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_xs_5450_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_v_5451_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5458_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5458_ == 0 {
                        v_unused_5459_ = crate::leanh::lean_ctor_get(v_x_5436_, 3);
                        crate::leanh::lean_dec(v_unused_5459_);
                        v___x_5453_ = v_x_5436_;
                        v_isShared_5454_ = v_isSharedCheck_5458_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_5451_);
                        crate::leanh::lean_inc(v_xs_5450_);
                        crate::leanh::lean_inc(v_j_5449_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5453_ = crate::leanh::lean_box(0);
                        v_isShared_5454_ = v_isSharedCheck_5458_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_x_5460_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_i_5461_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_y_5462_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5469_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5469_ == 0 {
                        v_unused_5470_ = crate::leanh::lean_ctor_get(v_x_5436_, 3);
                        crate::leanh::lean_dec(v_unused_5470_);
                        v___x_5464_ = v_x_5436_;
                        v_isShared_5465_ = v_isSharedCheck_5469_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_y_5462_);
                        crate::leanh::lean_inc(v_i_5461_);
                        crate::leanh::lean_inc(v_x_5460_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5464_ = crate::leanh::lean_box(0);
                        v_isShared_5465_ = v_isSharedCheck_5469_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_x_5471_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_i_5472_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_y_5473_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                    v_isSharedCheck_5480_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5480_ == 0 {
                        v_unused_5481_ = crate::leanh::lean_ctor_get(v_x_5436_, 3);
                        crate::leanh::lean_dec(v_unused_5481_);
                        v___x_5475_ = v_x_5436_;
                        v_isShared_5476_ = v_isSharedCheck_5480_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_y_5473_);
                        crate::leanh::lean_inc(v_i_5472_);
                        crate::leanh::lean_inc(v_x_5471_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5475_ = crate::leanh::lean_box(0);
                        v_isShared_5476_ = v_isSharedCheck_5480_;
                        state = 7;
                        continue;
                    }
                }
                5 => {
                    v_x_5482_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_i_5483_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_offset_5484_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                    v_y_5485_ = crate::leanh::lean_ctor_get(v_x_5436_, 3);
                    v_ty_5486_ = crate::leanh::lean_ctor_get(v_x_5436_, 4);
                    v_isSharedCheck_5493_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5493_ == 0 {
                        v_unused_5494_ = crate::leanh::lean_ctor_get(v_x_5436_, 5);
                        crate::leanh::lean_dec(v_unused_5494_);
                        v___x_5488_ = v_x_5436_;
                        v_isShared_5489_ = v_isSharedCheck_5493_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_ty_5486_);
                        crate::leanh::lean_inc(v_y_5485_);
                        crate::leanh::lean_inc(v_offset_5484_);
                        crate::leanh::lean_inc(v_i_5483_);
                        crate::leanh::lean_inc(v_x_5482_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5488_ = crate::leanh::lean_box(0);
                        v_isShared_5489_ = v_isSharedCheck_5493_;
                        state = 9;
                        continue;
                    }
                }
                3 => {
                    v_x_5495_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_cidx_5496_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_isSharedCheck_5503_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5503_ == 0 {
                        v_unused_5504_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                        crate::leanh::lean_dec(v_unused_5504_);
                        v___x_5498_ = v_x_5436_;
                        v_isShared_5499_ = v_isSharedCheck_5503_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cidx_5496_);
                        crate::leanh::lean_inc(v_x_5495_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5498_ = crate::leanh::lean_box(0);
                        v_isShared_5499_ = v_isSharedCheck_5503_;
                        state = 11;
                        continue;
                    }
                }
                6 => {
                    v_x_5505_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_n_5506_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_c_5507_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_5508_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_isSharedCheck_5515_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5515_ == 0 {
                        v_unused_5516_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                        crate::leanh::lean_dec(v_unused_5516_);
                        v___x_5510_ = v_x_5436_;
                        v_isShared_5511_ = v_isSharedCheck_5515_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_5506_);
                        crate::leanh::lean_inc(v_x_5505_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5510_ = crate::leanh::lean_box(0);
                        v_isShared_5511_ = v_isSharedCheck_5515_;
                        state = 13;
                        continue;
                    }
                }
                7 => {
                    v_x_5517_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_n_5518_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                    v_c_5519_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_persistent_5520_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_5436_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    );
                    v_isSharedCheck_5527_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5527_ == 0 {
                        v_unused_5528_ = crate::leanh::lean_ctor_get(v_x_5436_, 2);
                        crate::leanh::lean_dec(v_unused_5528_);
                        v___x_5522_ = v_x_5436_;
                        v_isShared_5523_ = v_isSharedCheck_5527_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_5518_);
                        crate::leanh::lean_inc(v_x_5517_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5522_ = crate::leanh::lean_box(0);
                        v_isShared_5523_ = v_isSharedCheck_5527_;
                        state = 15;
                        continue;
                    }
                }
                8 => {
                    v_x_5529_ = crate::leanh::lean_ctor_get(v_x_5436_, 0);
                    v_isSharedCheck_5536_ = (!crate::leanh::lean_is_exclusive(v_x_5436_)) as u8;
                    if v_isSharedCheck_5536_ == 0 {
                        v_unused_5537_ = crate::leanh::lean_ctor_get(v_x_5436_, 1);
                        crate::leanh::lean_dec(v_unused_5537_);
                        v___x_5531_ = v_x_5436_;
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_x_5529_);
                        crate::leanh::lean_dec(v_x_5436_);
                        v___x_5531_ = crate::leanh::lean_box(0);
                        v_isShared_5532_ = v_isSharedCheck_5536_;
                        state = 17;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_5437_);
                    return v_x_5436_;
                }
            },
            1 => {
                if v_isShared_5443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5442_, 3, v_x_5437_);
                    v___x_5445_ = v___x_5442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5446_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_x_5438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_ty_5439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5446_, 2, v_e_5440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5446_, 3, v_x_5437_);
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
                    crate::leanh::lean_ctor_set(v___x_5453_, 3, v_x_5437_);
                    v___x_5456_ = v___x_5453_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5457_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_j_5449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_xs_5450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 2, v_v_5451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 3, v_x_5437_);
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
                    crate::leanh::lean_ctor_set(v___x_5464_, 3, v_x_5437_);
                    v___x_5467_ = v___x_5464_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5468_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_x_5460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 1, v_i_5461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 2, v_y_5462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 3, v_x_5437_);
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
                    crate::leanh::lean_ctor_set(v___x_5475_, 3, v_x_5437_);
                    v___x_5478_ = v___x_5475_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5479_ = crate::leanh::lean_alloc_ctor(4, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_x_5471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 1, v_i_5472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 2, v_y_5473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 3, v_x_5437_);
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
                    crate::leanh::lean_ctor_set(v___x_5488_, 5, v_x_5437_);
                    v___x_5491_ = v___x_5488_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = crate::leanh::lean_alloc_ctor(5, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_x_5482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 1, v_i_5483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 2, v_offset_5484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 3, v_y_5485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 4, v_ty_5486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 5, v_x_5437_);
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
                    crate::leanh::lean_ctor_set(v___x_5498_, 2, v_x_5437_);
                    v___x_5501_ = v___x_5498_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5502_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_x_5495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5502_, 1, v_cidx_5496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5502_, 2, v_x_5437_);
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
                    crate::leanh::lean_ctor_set(v___x_5510_, 2, v_x_5437_);
                    v___x_5513_ = v___x_5510_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5514_ = crate::leanh::lean_alloc_ctor(6, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_x_5505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5514_, 1, v_n_5506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5514_, 2, v_x_5437_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5514_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_c_5507_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5514_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
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
                    crate::leanh::lean_ctor_set(v___x_5522_, 2, v_x_5437_);
                    v___x_5525_ = v___x_5522_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5526_ = crate::leanh::lean_alloc_ctor(7, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_x_5517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5526_, 1, v_n_5518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5526_, 2, v_x_5437_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5526_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_c_5519_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5526_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
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
                    crate::leanh::lean_ctor_set(v___x_5531_, 1, v_x_5437_);
                    v___x_5534_ = v___x_5531_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_x_5529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 1, v_x_5437_);
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
pub unsafe fn l_Lean_IR_FnBody_resetBody(
    mut v_b_5538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = crate::leanh::lean_box(12);
    v___x_5540_ = l_Lean_IR_FnBody_setBody(v_b_5538_, v___x_5539_);
    return v___x_5540_;
}
pub unsafe fn l_Lean_IR_FnBody_split(
    mut v_b_5541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_b_5541_) {
                0 => {
                    v_b_5547_ = crate::leanh::lean_ctor_get(v_b_5541_, 3);
                    crate::leanh::lean_inc(v_b_5547_);
                    v___y_5543_ = v_b_5547_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_b_5548_ = crate::leanh::lean_ctor_get(v_b_5541_, 3);
                    crate::leanh::lean_inc(v_b_5548_);
                    v___y_5543_ = v_b_5548_;
                    state = 1;
                    continue;
                }
                2 => {
                    v_b_5549_ = crate::leanh::lean_ctor_get(v_b_5541_, 3);
                    crate::leanh::lean_inc(v_b_5549_);
                    v___y_5543_ = v_b_5549_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_b_5550_ = crate::leanh::lean_ctor_get(v_b_5541_, 3);
                    crate::leanh::lean_inc(v_b_5550_);
                    v___y_5543_ = v_b_5550_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_b_5551_ = crate::leanh::lean_ctor_get(v_b_5541_, 5);
                    crate::leanh::lean_inc(v_b_5551_);
                    v___y_5543_ = v_b_5551_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_b_5552_ = crate::leanh::lean_ctor_get(v_b_5541_, 2);
                    crate::leanh::lean_inc(v_b_5552_);
                    v___y_5543_ = v_b_5552_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_b_5553_ = crate::leanh::lean_ctor_get(v_b_5541_, 2);
                    crate::leanh::lean_inc(v_b_5553_);
                    v___y_5543_ = v_b_5553_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_b_5554_ = crate::leanh::lean_ctor_get(v_b_5541_, 2);
                    crate::leanh::lean_inc(v_b_5554_);
                    v___y_5543_ = v_b_5554_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_b_5555_ = crate::leanh::lean_ctor_get(v_b_5541_, 1);
                    crate::leanh::lean_inc(v_b_5555_);
                    v___y_5543_ = v_b_5555_;
                    state = 1;
                    continue;
                }
                _ => {
                    crate::leanh::lean_inc(v_b_5541_);
                    v___y_5543_ = v_b_5541_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_5544_ = crate::leanh::lean_box(12);
                v_c_5545_ = l_Lean_IR_FnBody_setBody(v_b_5541_, v___x_5544_);
                v___x_5546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5546_, 0, v_c_5545_);
                crate::leanh::lean_ctor_set(v___x_5546_, 1, v___y_5543_);
                return v___x_5546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_IR_Alt_body(
    mut v_x_5556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5556_) == 0 {
        let mut v_b_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_b_5557_ = crate::leanh::lean_ctor_get(v_x_5556_, 1);
        crate::leanh::lean_inc(v_b_5557_);
        return v_b_5557_;
    } else {
        let mut v_b_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_b_5558_ = crate::leanh::lean_ctor_get(v_x_5556_, 0);
        crate::leanh::lean_inc(v_b_5558_);
        return v_b_5558_;
    }
}
pub unsafe fn l_Lean_IR_Alt_body___boxed(
    mut v_x_5559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5560_ = l_Lean_IR_Alt_body(v_x_5559_);
    crate::leanh::lean_dec_ref(v_x_5559_);
    return v_res_5560_;
}
pub unsafe fn l_Lean_IR_Alt_setBody(
    mut v_x_5561_: *mut crate::leanh::LeanObject,
    mut v_x_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut v_unused_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_unused_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5561_) == 0 {
                    v_info_5563_ = crate::leanh::lean_ctor_get(v_x_5561_, 0);
                    v_isSharedCheck_5570_ = (!crate::leanh::lean_is_exclusive(v_x_5561_)) as u8;
                    if v_isSharedCheck_5570_ == 0 {
                        v_unused_5571_ = crate::leanh::lean_ctor_get(v_x_5561_, 1);
                        crate::leanh::lean_dec(v_unused_5571_);
                        v___x_5565_ = v_x_5561_;
                        v_isShared_5566_ = v_isSharedCheck_5570_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_info_5563_);
                        crate::leanh::lean_dec(v_x_5561_);
                        v___x_5565_ = crate::leanh::lean_box(0);
                        v_isShared_5566_ = v_isSharedCheck_5570_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_5578_ = (!crate::leanh::lean_is_exclusive(v_x_5561_)) as u8;
                    if v_isSharedCheck_5578_ == 0 {
                        v_unused_5579_ = crate::leanh::lean_ctor_get(v_x_5561_, 0);
                        crate::leanh::lean_dec(v_unused_5579_);
                        v___x_5573_ = v_x_5561_;
                        v_isShared_5574_ = v_isSharedCheck_5578_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_x_5561_);
                        v___x_5573_ = crate::leanh::lean_box(0);
                        v_isShared_5574_ = v_isSharedCheck_5578_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5566_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5565_, 1, v_x_5562_);
                    v___x_5568_ = v___x_5565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5569_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_info_5563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 1, v_x_5562_);
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
                    crate::leanh::lean_ctor_set(v___x_5573_, 0, v_x_5562_);
                    v___x_5576_ = v___x_5573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_x_5562_);
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
    mut v_f_5580_: *mut crate::leanh::LeanObject,
    mut v_x_5581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5591_: u8 = 0;
    let mut v_b_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5595_: u8 = 0;
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5581_) == 0 {
                    v_info_5582_ = crate::leanh::lean_ctor_get(v_x_5581_, 0);
                    v_b_5583_ = crate::leanh::lean_ctor_get(v_x_5581_, 1);
                    v_isSharedCheck_5591_ = (!crate::leanh::lean_is_exclusive(v_x_5581_)) as u8;
                    if v_isSharedCheck_5591_ == 0 {
                        v___x_5585_ = v_x_5581_;
                        v_isShared_5586_ = v_isSharedCheck_5591_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_5583_);
                        crate::leanh::lean_inc(v_info_5582_);
                        crate::leanh::lean_dec(v_x_5581_);
                        v___x_5585_ = crate::leanh::lean_box(0);
                        v_isShared_5586_ = v_isSharedCheck_5591_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_b_5592_ = crate::leanh::lean_ctor_get(v_x_5581_, 0);
                    v_isSharedCheck_5600_ = (!crate::leanh::lean_is_exclusive(v_x_5581_)) as u8;
                    if v_isSharedCheck_5600_ == 0 {
                        v___x_5594_ = v_x_5581_;
                        v_isShared_5595_ = v_isSharedCheck_5600_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_5592_);
                        crate::leanh::lean_dec(v_x_5581_);
                        v___x_5594_ = crate::leanh::lean_box(0);
                        v_isShared_5595_ = v_isSharedCheck_5600_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5587_ = crate::leanh::lean_apply_1(v_f_5580_, v_b_5583_);
                if v_isShared_5586_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5585_, 1, v___x_5587_);
                    v___x_5589_ = v___x_5585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_info_5582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5587_);
                    v___x_5589_ = v_reuseFailAlloc_5590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5589_;
            }
            3 => {
                v___x_5596_ = crate::leanh::lean_apply_1(v_f_5580_, v_b_5592_);
                if v_isShared_5595_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5594_, 0, v___x_5596_);
                    v___x_5598_ = v___x_5594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5599_, 0, v___x_5596_);
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
    mut v_info_5601_: *mut crate::leanh::LeanObject,
    mut v_b_5602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5603_, 0, v_info_5601_);
    crate::leanh::lean_ctor_set(v___x_5603_, 1, v_b_5602_);
    return v___x_5603_;
}
pub unsafe fn l_Lean_IR_Alt_modifyBodyM___redArg___lam__1(
    mut v_b_5604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5605_, 0, v_b_5604_);
    return v___x_5605_;
}
pub unsafe fn l_Lean_IR_Alt_modifyBodyM___redArg(
    mut v_inst_5607_: *mut crate::leanh::LeanObject,
    mut v_f_5608_: *mut crate::leanh::LeanObject,
    mut v_x_5609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5610_ = crate::leanh::lean_ctor_get(v_inst_5607_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5610_);
    crate::leanh::lean_dec_ref(v_inst_5607_);
    if crate::leanh::lean_obj_tag(v_x_5609_) == 0 {
        let mut v_toFunctor_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_info_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_b_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_5611_ = crate::leanh::lean_ctor_get(v_toApplicative_5610_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_5611_);
        crate::leanh::lean_dec_ref(v_toApplicative_5610_);
        v_info_5612_ = crate::leanh::lean_ctor_get(v_x_5609_, 0);
        crate::leanh::lean_inc_ref(v_info_5612_);
        v_b_5613_ = crate::leanh::lean_ctor_get(v_x_5609_, 1);
        crate::leanh::lean_inc(v_b_5613_);
        crate::leanh::lean_dec_ref_known(v_x_5609_, 2);
        v_map_5614_ = crate::leanh::lean_ctor_get(v_toFunctor_5611_, 0);
        crate::leanh::lean_inc(v_map_5614_);
        crate::leanh::lean_dec_ref(v_toFunctor_5611_);
        v___f_5615_ = crate::leanh::lean_alloc_closure(
            l_Lean_IR_Alt_modifyBodyM___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5615_, 0, v_info_5612_);
        v___x_5616_ = crate::leanh::lean_apply_1(v_f_5608_, v_b_5613_);
        v___x_5617_ = crate::leanh::lean_apply_4(
            v_map_5614_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_5615_,
            v___x_5616_,
        );
        return v___x_5617_;
    } else {
        let mut v_toFunctor_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_b_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_5618_ = crate::leanh::lean_ctor_get(v_toApplicative_5610_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_5618_);
        crate::leanh::lean_dec_ref(v_toApplicative_5610_);
        v_b_5619_ = crate::leanh::lean_ctor_get(v_x_5609_, 0);
        crate::leanh::lean_inc(v_b_5619_);
        crate::leanh::lean_dec_ref_known(v_x_5609_, 1);
        v_map_5620_ = crate::leanh::lean_ctor_get(v_toFunctor_5618_, 0);
        crate::leanh::lean_inc(v_map_5620_);
        crate::leanh::lean_dec_ref(v_toFunctor_5618_);
        v___f_5621_ = l_Lean_IR_Alt_modifyBodyM___redArg___closed__0;
        v___x_5622_ = crate::leanh::lean_apply_1(v_f_5608_, v_b_5619_);
        v___x_5623_ = crate::leanh::lean_apply_4(
            v_map_5620_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_5621_,
            v___x_5622_,
        );
        return v___x_5623_;
    }
}
pub unsafe fn l_Lean_IR_Alt_modifyBodyM(
    mut v_m_5624_: *mut crate::leanh::LeanObject,
    mut v_inst_5625_: *mut crate::leanh::LeanObject,
    mut v_f_5626_: *mut crate::leanh::LeanObject,
    mut v_x_5627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5628_ = crate::leanh::lean_ctor_get(v_inst_5625_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_5628_);
    crate::leanh::lean_dec_ref(v_inst_5625_);
    if crate::leanh::lean_obj_tag(v_x_5627_) == 0 {
        let mut v_toFunctor_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_info_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_b_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_5629_ = crate::leanh::lean_ctor_get(v_toApplicative_5628_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_5629_);
        crate::leanh::lean_dec_ref(v_toApplicative_5628_);
        v_info_5630_ = crate::leanh::lean_ctor_get(v_x_5627_, 0);
        crate::leanh::lean_inc_ref(v_info_5630_);
        v_b_5631_ = crate::leanh::lean_ctor_get(v_x_5627_, 1);
        crate::leanh::lean_inc(v_b_5631_);
        crate::leanh::lean_dec_ref_known(v_x_5627_, 2);
        v_map_5632_ = crate::leanh::lean_ctor_get(v_toFunctor_5629_, 0);
        crate::leanh::lean_inc(v_map_5632_);
        crate::leanh::lean_dec_ref(v_toFunctor_5629_);
        v___f_5633_ = crate::leanh::lean_alloc_closure(
            l_Lean_IR_Alt_modifyBodyM___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_5633_, 0, v_info_5630_);
        v___x_5634_ = crate::leanh::lean_apply_1(v_f_5626_, v_b_5631_);
        v___x_5635_ = crate::leanh::lean_apply_4(
            v_map_5632_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_5633_,
            v___x_5634_,
        );
        return v___x_5635_;
    } else {
        let mut v_toFunctor_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_b_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_5636_ = crate::leanh::lean_ctor_get(v_toApplicative_5628_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_5636_);
        crate::leanh::lean_dec_ref(v_toApplicative_5628_);
        v_b_5637_ = crate::leanh::lean_ctor_get(v_x_5627_, 0);
        crate::leanh::lean_inc(v_b_5637_);
        crate::leanh::lean_dec_ref_known(v_x_5627_, 1);
        v_map_5638_ = crate::leanh::lean_ctor_get(v_toFunctor_5636_, 0);
        crate::leanh::lean_inc(v_map_5638_);
        crate::leanh::lean_dec_ref(v_toFunctor_5636_);
        v___f_5639_ = l_Lean_IR_Alt_modifyBodyM___redArg___closed__0;
        v___x_5640_ = crate::leanh::lean_apply_1(v_f_5626_, v_b_5637_);
        v___x_5641_ = crate::leanh::lean_apply_4(
            v_map_5638_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_5639_,
            v___x_5640_,
        );
        return v___x_5641_;
    }
}
pub unsafe fn l_Lean_IR_Alt_isDefault(mut v_x_5642_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5642_) == 0 {
        let mut v___x_5643_: u8 = 0;
        v___x_5643_ = 0;
        return v___x_5643_;
    } else {
        let mut v___x_5644_: u8 = 0;
        v___x_5644_ = 1;
        return v___x_5644_;
    }
}
pub unsafe fn l_Lean_IR_Alt_isDefault___boxed(
    mut v_x_5645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5646_: u8 = 0;
    let mut v_r_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5646_ = l_Lean_IR_Alt_isDefault(v_x_5645_);
    crate::leanh::lean_dec_ref(v_x_5645_);
    v_r_5647_ = crate::leanh::lean_box((v_res_5646_) as usize);
    return v_r_5647_;
}
pub unsafe fn l_Lean_IR_push(
    mut v_bs_5648_: *mut crate::leanh::LeanObject,
    mut v_b_5649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5650_ = crate::leanh::lean_box(12);
    v_b_5651_ = l_Lean_IR_FnBody_setBody(v_b_5649_, v___x_5650_);
    v___x_5652_ = lean_array_push(v_bs_5648_, v_b_5651_);
    return v___x_5652_;
}
pub unsafe fn l_Lean_IR_flattenAux(
    mut v_b_5653_: *mut crate::leanh::LeanObject,
    mut v_r_5654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: u8 = 0;
    let mut v_b_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5659_ = l_Lean_IR_FnBody_isTerminal(v_b_5653_);
                if v___x_5659_ == 0 {
                    match crate::leanh::lean_obj_tag(v_b_5653_) {
                        0 => {
                            v_b_5660_ = crate::leanh::lean_ctor_get(v_b_5653_, 3);
                            crate::leanh::lean_inc(v_b_5660_);
                            v___y_5656_ = v_b_5660_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_b_5661_ = crate::leanh::lean_ctor_get(v_b_5653_, 3);
                            crate::leanh::lean_inc(v_b_5661_);
                            v___y_5656_ = v_b_5661_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_b_5662_ = crate::leanh::lean_ctor_get(v_b_5653_, 3);
                            crate::leanh::lean_inc(v_b_5662_);
                            v___y_5656_ = v_b_5662_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v_b_5663_ = crate::leanh::lean_ctor_get(v_b_5653_, 3);
                            crate::leanh::lean_inc(v_b_5663_);
                            v___y_5656_ = v_b_5663_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v_b_5664_ = crate::leanh::lean_ctor_get(v_b_5653_, 5);
                            crate::leanh::lean_inc(v_b_5664_);
                            v___y_5656_ = v_b_5664_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            v_b_5665_ = crate::leanh::lean_ctor_get(v_b_5653_, 2);
                            crate::leanh::lean_inc(v_b_5665_);
                            v___y_5656_ = v_b_5665_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_b_5666_ = crate::leanh::lean_ctor_get(v_b_5653_, 2);
                            crate::leanh::lean_inc(v_b_5666_);
                            v___y_5656_ = v_b_5666_;
                            state = 1;
                            continue;
                        }
                        7 => {
                            v_b_5667_ = crate::leanh::lean_ctor_get(v_b_5653_, 2);
                            crate::leanh::lean_inc(v_b_5667_);
                            v___y_5656_ = v_b_5667_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_b_5668_ = crate::leanh::lean_ctor_get(v_b_5653_, 1);
                            crate::leanh::lean_inc(v_b_5668_);
                            v___y_5656_ = v_b_5668_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_inc(v_b_5653_);
                            v___y_5656_ = v_b_5653_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5669_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5669_, 0, v_r_5654_);
                    crate::leanh::lean_ctor_set(v___x_5669_, 1, v_b_5653_);
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
pub unsafe fn l_Lean_IR_FnBody_flatten(
    mut v_b_5672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5673_ = l_Lean_IR_FnBody_flatten___closed__0;
    v___x_5674_ = l_Lean_IR_flattenAux(v_b_5672_, v___x_5673_);
    return v___x_5674_;
}
pub unsafe fn l_panic___at___00Lean_IR_reshapeAux_spec__0(
    mut v___x_5675_: *mut crate::leanh::LeanObject,
    mut v_msg_5676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5677_ = lean_panic_fn_borrowed(v___x_5675_, v_msg_5676_);
    return v___x_5677_;
}
pub unsafe fn l_panic___at___00Lean_IR_reshapeAux_spec__0___boxed(
    mut v___x_5678_: *mut crate::leanh::LeanObject,
    mut v_msg_5679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5680_ = l_panic___at___00Lean_IR_reshapeAux_spec__0(v___x_5678_, v_msg_5679_);
    crate::leanh::lean_dec_ref(v___x_5678_);
    return v_res_5680_;
}
pub unsafe fn l_Lean_IR_reshapeAux(
    mut v_a_5685_: *mut crate::leanh::LeanObject,
    mut v_i_5686_: *mut crate::leanh::LeanObject,
    mut v_b_5687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    let mut v___x_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: u8 = 0;
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5688_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5689_ = lean_nat_dec_eq(v_i_5686_, v___x_5688_);
                if v___x_5689_ == 0 {
                    v___x_5690_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_i_5691_ = lean_nat_sub(v_i_5686_, v___x_5690_);
                    crate::leanh::lean_dec(v_i_5686_);
                    v___x_5697_ = l_Lean_IR_instInhabitedFnBody_default__1;
                    v___x_5698_ = lean_array_get_size(v_a_5685_);
                    v___x_5699_ = lean_nat_dec_lt(v_i_5691_, v___x_5698_);
                    if v___x_5699_ == 0 {
                        v___x_5700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5700_, 0, v___x_5697_);
                        crate::leanh::lean_ctor_set(v___x_5700_, 1, v_a_5685_);
                        v___x_5701_ = l_Lean_IR_reshapeAux___closed__0;
                        v___x_5702_ = l_Lean_IR_reshapeAux___closed__1;
                        v___x_5703_ = crate::leanh::lean_unsigned_to_nat(438);
                        v___x_5704_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___x_5705_ = l_Lean_IR_reshapeAux___closed__2;
                        crate::leanh::lean_inc(v_i_5691_);
                        v___x_5706_ = l_Nat_reprFast(v_i_5691_);
                        v___x_5707_ = lean_string_append(v___x_5705_, v___x_5706_);
                        crate::leanh::lean_dec_ref(v___x_5706_);
                        v___x_5708_ = l_Lean_IR_reshapeAux___closed__3;
                        v___x_5709_ = lean_string_append(v___x_5707_, v___x_5708_);
                        v___x_5710_ = l_mkPanicMessageWithDecl(
                            v___x_5701_,
                            v___x_5702_,
                            v___x_5703_,
                            v___x_5704_,
                            v___x_5709_,
                        );
                        crate::leanh::lean_dec_ref(v___x_5709_);
                        v___x_5711_ = lean_panic_fn_borrowed(v___x_5700_, v___x_5710_);
                        crate::leanh::lean_dec_ref_known(v___x_5700_, 2);
                        v_fst_5712_ = crate::leanh::lean_ctor_get(v___x_5711_, 0);
                        crate::leanh::lean_inc(v_fst_5712_);
                        v_snd_5713_ = crate::leanh::lean_ctor_get(v___x_5711_, 1);
                        crate::leanh::lean_inc(v_snd_5713_);
                        crate::leanh::lean_dec(v___x_5711_);
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
                    crate::leanh::lean_dec(v_i_5686_);
                    crate::leanh::lean_dec_ref(v_a_5685_);
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
    mut v_bs_5716_: *mut crate::leanh::LeanObject,
    mut v_term_5717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5718_ = lean_array_get_size(v_bs_5716_);
    v___x_5719_ = l_Lean_IR_reshapeAux(v_bs_5716_, v___x_5718_, v_term_5717_);
    return v___x_5719_;
}
pub unsafe fn l_Lean_IR_modifyJPs___lam__0(
    mut v_f_5720_: *mut crate::leanh::LeanObject,
    mut v_x_5721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_j_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5728_: u8 = 0;
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5721_) == 1 {
                    v_j_5722_ = crate::leanh::lean_ctor_get(v_x_5721_, 0);
                    v_xs_5723_ = crate::leanh::lean_ctor_get(v_x_5721_, 1);
                    v_v_5724_ = crate::leanh::lean_ctor_get(v_x_5721_, 2);
                    v_b_5725_ = crate::leanh::lean_ctor_get(v_x_5721_, 3);
                    v_isSharedCheck_5733_ = (!crate::leanh::lean_is_exclusive(v_x_5721_)) as u8;
                    if v_isSharedCheck_5733_ == 0 {
                        v___x_5727_ = v_x_5721_;
                        v_isShared_5728_ = v_isSharedCheck_5733_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_b_5725_);
                        crate::leanh::lean_inc(v_v_5724_);
                        crate::leanh::lean_inc(v_xs_5723_);
                        crate::leanh::lean_inc(v_j_5722_);
                        crate::leanh::lean_dec(v_x_5721_);
                        v___x_5727_ = crate::leanh::lean_box(0);
                        v_isShared_5728_ = v_isSharedCheck_5733_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_5720_);
                    return v_x_5721_;
                }
            }
            1 => {
                v___x_5729_ = crate::leanh::lean_apply_1(v_f_5720_, v_v_5724_);
                if v_isShared_5728_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5727_, 2, v___x_5729_);
                    v___x_5731_ = v___x_5727_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5732_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_j_5722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 1, v_xs_5723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 2, v___x_5729_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 3, v_b_5725_);
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
    mut v_bs_5753_: *mut crate::leanh::LeanObject,
    mut v_f_5754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5757_: usize = 0;
    let mut v___x_5758_: usize = 0;
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5755_ = crate::leanh::lean_alloc_closure(
        l_Lean_IR_modifyJPs___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_5755_, 0, v_f_5754_);
    v___x_5756_ = l_Lean_IR_modifyJPs___closed__9;
    v_sz_5757_ = lean_array_size(v_bs_5753_);
    v___x_5758_ = 0usize;
    v___x_5759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5756_,
        v___f_5755_,
        v_sz_5757_,
        v___x_5758_,
        v_bs_5753_,
    );
    return v___x_5759_;
}
pub unsafe fn l_Lean_IR_modifyJPsM___redArg___lam__0(
    mut v_j_5760_: *mut crate::leanh::LeanObject,
    mut v_xs_5761_: *mut crate::leanh::LeanObject,
    mut v_b_5762_: *mut crate::leanh::LeanObject,
    mut v_toPure_5763_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_5764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5765_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5765_, 0, v_j_5760_);
    crate::leanh::lean_ctor_set(v___x_5765_, 1, v_xs_5761_);
    crate::leanh::lean_ctor_set(v___x_5765_, 2, v_____do__lift_5764_);
    crate::leanh::lean_ctor_set(v___x_5765_, 3, v_b_5762_);
    v___x_5766_ =
        crate::leanh::lean_apply_2(v_toPure_5763_, crate::leanh::lean_box(0), v___x_5765_);
    return v___x_5766_;
}
pub unsafe fn l_Lean_IR_modifyJPsM___redArg___lam__1(
    mut v_toPure_5767_: *mut crate::leanh::LeanObject,
    mut v_f_5768_: *mut crate::leanh::LeanObject,
    mut v_toBind_5769_: *mut crate::leanh::LeanObject,
    mut v_b_5770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_5770_) == 1 {
        let mut v_j_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_b_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_j_5771_ = crate::leanh::lean_ctor_get(v_b_5770_, 0);
        crate::leanh::lean_inc(v_j_5771_);
        v_xs_5772_ = crate::leanh::lean_ctor_get(v_b_5770_, 1);
        crate::leanh::lean_inc_ref(v_xs_5772_);
        v_v_5773_ = crate::leanh::lean_ctor_get(v_b_5770_, 2);
        crate::leanh::lean_inc(v_v_5773_);
        v_b_5774_ = crate::leanh::lean_ctor_get(v_b_5770_, 3);
        crate::leanh::lean_inc(v_b_5774_);
        crate::leanh::lean_dec_ref_known(v_b_5770_, 4);
        v___f_5775_ = crate::leanh::lean_alloc_closure(
            l_Lean_IR_modifyJPsM___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_5775_, 0, v_j_5771_);
        crate::leanh::lean_closure_set(v___f_5775_, 1, v_xs_5772_);
        crate::leanh::lean_closure_set(v___f_5775_, 2, v_b_5774_);
        crate::leanh::lean_closure_set(v___f_5775_, 3, v_toPure_5767_);
        v___x_5776_ = crate::leanh::lean_apply_1(v_f_5768_, v_v_5773_);
        v___x_5777_ = crate::leanh::lean_apply_4(
            v_toBind_5769_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_5776_,
            v___f_5775_,
        );
        return v___x_5777_;
    } else {
        let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_5769_);
        crate::leanh::lean_dec(v_f_5768_);
        v___x_5778_ =
            crate::leanh::lean_apply_2(v_toPure_5767_, crate::leanh::lean_box(0), v_b_5770_);
        return v___x_5778_;
    }
}
pub unsafe fn l_Lean_IR_modifyJPsM___redArg(
    mut v_inst_5779_: *mut crate::leanh::LeanObject,
    mut v_bs_5780_: *mut crate::leanh::LeanObject,
    mut v_f_5781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5786_: usize = 0;
    let mut v___x_5787_: usize = 0;
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5782_ = crate::leanh::lean_ctor_get(v_inst_5779_, 0);
    v_toBind_5783_ = crate::leanh::lean_ctor_get(v_inst_5779_, 1);
    v_toPure_5784_ = crate::leanh::lean_ctor_get(v_toApplicative_5782_, 1);
    crate::leanh::lean_inc(v_toBind_5783_);
    crate::leanh::lean_inc(v_toPure_5784_);
    v___f_5785_ = crate::leanh::lean_alloc_closure(
        l_Lean_IR_modifyJPsM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5785_, 0, v_toPure_5784_);
    crate::leanh::lean_closure_set(v___f_5785_, 1, v_f_5781_);
    crate::leanh::lean_closure_set(v___f_5785_, 2, v_toBind_5783_);
    v_sz_5786_ = lean_array_size(v_bs_5780_);
    v___x_5787_ = 0usize;
    v___x_5788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5779_,
        v___f_5785_,
        v_sz_5786_,
        v___x_5787_,
        v_bs_5780_,
    );
    return v___x_5788_;
}
pub unsafe fn l_Lean_IR_modifyJPsM(
    mut v_m_5789_: *mut crate::leanh::LeanObject,
    mut v_inst_5790_: *mut crate::leanh::LeanObject,
    mut v_bs_5791_: *mut crate::leanh::LeanObject,
    mut v_f_5792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5797_: usize = 0;
    let mut v___x_5798_: usize = 0;
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_5793_ = crate::leanh::lean_ctor_get(v_inst_5790_, 0);
    v_toBind_5794_ = crate::leanh::lean_ctor_get(v_inst_5790_, 1);
    v_toPure_5795_ = crate::leanh::lean_ctor_get(v_toApplicative_5793_, 1);
    crate::leanh::lean_inc(v_toBind_5794_);
    crate::leanh::lean_inc(v_toPure_5795_);
    v___f_5796_ = crate::leanh::lean_alloc_closure(
        l_Lean_IR_modifyJPsM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_5796_, 0, v_toPure_5795_);
    crate::leanh::lean_closure_set(v___f_5796_, 1, v_f_5792_);
    crate::leanh::lean_closure_set(v___f_5796_, 2, v_toBind_5794_);
    v_sz_5797_ = lean_array_size(v_bs_5791_);
    v___x_5798_ = 0usize;
    v___x_5799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_5790_,
        v___f_5796_,
        v_sz_5797_,
        v___x_5798_,
        v_bs_5791_,
    );
    return v___x_5799_;
}
pub unsafe fn l_Lean_IR_Decl_ctorIdx(
    mut v_x_5800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5800_) == 0 {
        let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5801_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_5801_;
    } else {
        let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5802_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_5802_;
    }
}
pub unsafe fn l_Lean_IR_Decl_ctorIdx___boxed(
    mut v_x_5803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5804_ = l_Lean_IR_Decl_ctorIdx(v_x_5803_);
    crate::leanh::lean_dec_ref(v_x_5803_);
    return v_res_5804_;
}
pub unsafe fn l_Lean_IR_Decl_ctorElim___redArg(
    mut v_t_5805_: *mut crate::leanh::LeanObject,
    mut v_k_5806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_5805_) == 0 {
        let mut v_f_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_info_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_f_5807_ = crate::leanh::lean_ctor_get(v_t_5805_, 0);
        crate::leanh::lean_inc(v_f_5807_);
        v_xs_5808_ = crate::leanh::lean_ctor_get(v_t_5805_, 1);
        crate::leanh::lean_inc_ref(v_xs_5808_);
        v_type_5809_ = crate::leanh::lean_ctor_get(v_t_5805_, 2);
        crate::leanh::lean_inc(v_type_5809_);
        v_body_5810_ = crate::leanh::lean_ctor_get(v_t_5805_, 3);
        crate::leanh::lean_inc(v_body_5810_);
        v_info_5811_ = crate::leanh::lean_ctor_get(v_t_5805_, 4);
        crate::leanh::lean_inc(v_info_5811_);
        crate::leanh::lean_dec_ref_known(v_t_5805_, 5);
        v___x_5812_ = crate::leanh::lean_apply_5(
            v_k_5806_,
            v_f_5807_,
            v_xs_5808_,
            v_type_5809_,
            v_body_5810_,
            v_info_5811_,
        );
        return v___x_5812_;
    } else {
        let mut v_f_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_ext_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_f_5813_ = crate::leanh::lean_ctor_get(v_t_5805_, 0);
        crate::leanh::lean_inc(v_f_5813_);
        v_xs_5814_ = crate::leanh::lean_ctor_get(v_t_5805_, 1);
        crate::leanh::lean_inc_ref(v_xs_5814_);
        v_type_5815_ = crate::leanh::lean_ctor_get(v_t_5805_, 2);
        crate::leanh::lean_inc(v_type_5815_);
        v_ext_5816_ = crate::leanh::lean_ctor_get(v_t_5805_, 3);
        crate::leanh::lean_inc(v_ext_5816_);
        crate::leanh::lean_dec_ref_known(v_t_5805_, 4);
        v___x_5817_ =
            crate::leanh::lean_apply_4(v_k_5806_, v_f_5813_, v_xs_5814_, v_type_5815_, v_ext_5816_);
        return v___x_5817_;
    }
}
pub unsafe fn l_Lean_IR_Decl_ctorElim(
    mut v_motive_5818_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5819_: *mut crate::leanh::LeanObject,
    mut v_t_5820_: *mut crate::leanh::LeanObject,
    mut v_h_5821_: *mut crate::leanh::LeanObject,
    mut v_k_5822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5823_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5820_, v_k_5822_);
    return v___x_5823_;
}
pub unsafe fn l_Lean_IR_Decl_ctorElim___boxed(
    mut v_motive_5824_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_5825_: *mut crate::leanh::LeanObject,
    mut v_t_5826_: *mut crate::leanh::LeanObject,
    mut v_h_5827_: *mut crate::leanh::LeanObject,
    mut v_k_5828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5829_ = l_Lean_IR_Decl_ctorElim(
        v_motive_5824_,
        v_ctorIdx_5825_,
        v_t_5826_,
        v_h_5827_,
        v_k_5828_,
    );
    crate::leanh::lean_dec(v_ctorIdx_5825_);
    return v_res_5829_;
}
pub unsafe fn l_Lean_IR_Decl_fdecl_elim___redArg(
    mut v_t_5830_: *mut crate::leanh::LeanObject,
    mut v_fdecl_5831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5832_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5830_, v_fdecl_5831_);
    return v___x_5832_;
}
pub unsafe fn l_Lean_IR_Decl_fdecl_elim(
    mut v_motive_5833_: *mut crate::leanh::LeanObject,
    mut v_t_5834_: *mut crate::leanh::LeanObject,
    mut v_h_5835_: *mut crate::leanh::LeanObject,
    mut v_fdecl_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5837_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5834_, v_fdecl_5836_);
    return v___x_5837_;
}
pub unsafe fn l_Lean_IR_Decl_extern_elim___redArg(
    mut v_t_5838_: *mut crate::leanh::LeanObject,
    mut v_extern_5839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5840_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5838_, v_extern_5839_);
    return v___x_5840_;
}
pub unsafe fn l_Lean_IR_Decl_extern_elim(
    mut v_motive_5841_: *mut crate::leanh::LeanObject,
    mut v_t_5842_: *mut crate::leanh::LeanObject,
    mut v_h_5843_: *mut crate::leanh::LeanObject,
    mut v_extern_5844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5845_ = l_Lean_IR_Decl_ctorElim___redArg(v_t_5842_, v_extern_5844_);
    return v___x_5845_;
}
pub unsafe fn l_Lean_IR_Decl_name(
    mut v_x_5855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_f_5856_ = crate::leanh::lean_ctor_get(v_x_5855_, 0);
    crate::leanh::lean_inc(v_f_5856_);
    return v_f_5856_;
}
pub unsafe fn l_Lean_IR_Decl_name___boxed(
    mut v_x_5857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_IR_Decl_name(v_x_5857_);
    crate::leanh::lean_dec_ref(v_x_5857_);
    return v_res_5858_;
}
pub unsafe fn l_Lean_IR_Decl_params(
    mut v_x_5859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_xs_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_xs_5860_ = crate::leanh::lean_ctor_get(v_x_5859_, 1);
    crate::leanh::lean_inc_ref(v_xs_5860_);
    return v_xs_5860_;
}
pub unsafe fn l_Lean_IR_Decl_params___boxed(
    mut v_x_5861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5862_ = l_Lean_IR_Decl_params(v_x_5861_);
    crate::leanh::lean_dec_ref(v_x_5861_);
    return v_res_5862_;
}
pub unsafe fn l_Lean_IR_Decl_resultType(
    mut v_x_5863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_5864_ = crate::leanh::lean_ctor_get(v_x_5863_, 2);
    crate::leanh::lean_inc(v_type_5864_);
    return v_type_5864_;
}
pub unsafe fn l_Lean_IR_Decl_resultType___boxed(
    mut v_x_5865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5866_ = l_Lean_IR_Decl_resultType(v_x_5865_);
    crate::leanh::lean_dec_ref(v_x_5865_);
    return v_res_5866_;
}
pub unsafe fn l_Lean_IR_Decl_isExtern(mut v_x_5867_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5867_) == 1 {
        let mut v___x_5868_: u8 = 0;
        v___x_5868_ = 1;
        return v___x_5868_;
    } else {
        let mut v___x_5869_: u8 = 0;
        v___x_5869_ = 0;
        return v___x_5869_;
    }
}
pub unsafe fn l_Lean_IR_Decl_isExtern___boxed(
    mut v_x_5870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5871_: u8 = 0;
    let mut v_r_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5871_ = l_Lean_IR_Decl_isExtern(v_x_5870_);
    crate::leanh::lean_dec_ref(v_x_5870_);
    v_r_5872_ = crate::leanh::lean_box((v_res_5871_) as usize);
    return v_r_5872_;
}
pub unsafe fn l_Lean_IR_Decl_getInfo(
    mut v_x_5873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_5873_) == 0 {
        let mut v_info_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_info_5874_ = crate::leanh::lean_ctor_get(v_x_5873_, 4);
        crate::leanh::lean_inc(v_info_5874_);
        return v_info_5874_;
    } else {
        let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5875_ = crate::leanh::lean_box(0);
        return v___x_5875_;
    }
}
pub unsafe fn l_Lean_IR_Decl_getInfo___boxed(
    mut v_x_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5877_ = l_Lean_IR_Decl_getInfo(v_x_5876_);
    crate::leanh::lean_dec_ref(v_x_5876_);
    return v_res_5877_;
}
pub unsafe fn l_panic___at___00Lean_IR_Decl_updateBody_x21_spec__0(
    mut v_msg_5878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5879_ = l_Lean_IR_instInhabitedDecl_default;
    v___x_5880_ = lean_panic_fn_borrowed(v___x_5879_, v_msg_5878_);
    return v___x_5880_;
}
pub unsafe fn _init_l_Lean_IR_Decl_updateBody_x21___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5884_ = l_Lean_IR_Decl_updateBody_x21___closed__2;
    v___x_5885_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_5886_ = crate::leanh::lean_unsigned_to_nat(382);
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
    mut v_d_5890_: *mut crate::leanh::LeanObject,
    mut v_bNew_5891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut v_unused_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_d_5890_) == 0 {
                    v_f_5892_ = crate::leanh::lean_ctor_get(v_d_5890_, 0);
                    v_xs_5893_ = crate::leanh::lean_ctor_get(v_d_5890_, 1);
                    v_type_5894_ = crate::leanh::lean_ctor_get(v_d_5890_, 2);
                    v_info_5895_ = crate::leanh::lean_ctor_get(v_d_5890_, 4);
                    v_isSharedCheck_5902_ = (!crate::leanh::lean_is_exclusive(v_d_5890_)) as u8;
                    if v_isSharedCheck_5902_ == 0 {
                        v_unused_5903_ = crate::leanh::lean_ctor_get(v_d_5890_, 3);
                        crate::leanh::lean_dec(v_unused_5903_);
                        v___x_5897_ = v_d_5890_;
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_info_5895_);
                        crate::leanh::lean_inc(v_type_5894_);
                        crate::leanh::lean_inc(v_xs_5893_);
                        crate::leanh::lean_inc(v_f_5892_);
                        crate::leanh::lean_dec(v_d_5890_);
                        v___x_5897_ = crate::leanh::lean_box(0);
                        v_isShared_5898_ = v_isSharedCheck_5902_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_bNew_5891_);
                    crate::leanh::lean_dec_ref(v_d_5890_);
                    v___x_5904_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set(v___x_5897_, 3, v_bNew_5891_);
                    v___x_5900_ = v___x_5897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_f_5892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 1, v_xs_5893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 2, v_type_5894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 3, v_bNew_5891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 4, v_info_5895_);
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
    mut v_f_5906_: *mut crate::leanh::LeanObject,
    mut v_xs_5907_: *mut crate::leanh::LeanObject,
    mut v_ty_5908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5909_ = crate::leanh::lean_box(12);
    v___x_5910_ = crate::leanh::lean_box(0);
    v___x_5911_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5911_, 0, v_f_5906_);
    crate::leanh::lean_ctor_set(v___x_5911_, 1, v_xs_5907_);
    crate::leanh::lean_ctor_set(v___x_5911_, 2, v_ty_5908_);
    crate::leanh::lean_ctor_set(v___x_5911_, 3, v___x_5909_);
    crate::leanh::lean_ctor_set(v___x_5911_, 4, v___x_5910_);
    return v___x_5911_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
    mut v_k_5912_: *mut crate::leanh::LeanObject,
    mut v_v_5913_: *mut crate::leanh::LeanObject,
    mut v_t_5914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v___x_5923_: u8 = 0;
    let mut v___x_5924_: u8 = 0;
    let mut v_impl_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5943_: u8 = 0;
    let mut v_size_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: u8 = 0;
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5955_: u8 = 0;
    let mut v___x_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5980_: u8 = 0;
    let mut v_unused_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5993_: u8 = 0;
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5997_: u8 = 0;
    let mut v_unused_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6004_: u8 = 0;
    let mut v_unused_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v_k_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6021_: u8 = 0;
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6032_: u8 = 0;
    let mut v_unused_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6036_: u8 = 0;
    let mut v_unused_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6044_: u8 = 0;
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_unused_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: u8 = 0;
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6081_: u8 = 0;
    let mut v_size_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: u8 = 0;
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6093_: u8 = 0;
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6119_: u8 = 0;
    let mut v_unused_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6133_: u8 = 0;
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6137_: u8 = 0;
    let mut v_unused_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6144_: u8 = 0;
    let mut v_unused_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6156_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6164_: u8 = 0;
    let mut v_unused_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6172_: u8 = 0;
    let mut v_k_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6177_: u8 = 0;
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6188_: u8 = 0;
    let mut v_unused_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6192_: u8 = 0;
    let mut v_unused_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6200_: u8 = 0;
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_5914_) == 0 {
                    v_size_5915_ = crate::leanh::lean_ctor_get(v_t_5914_, 0);
                    v_k_5916_ = crate::leanh::lean_ctor_get(v_t_5914_, 1);
                    v_v_5917_ = crate::leanh::lean_ctor_get(v_t_5914_, 2);
                    v_l_5918_ = crate::leanh::lean_ctor_get(v_t_5914_, 3);
                    v_r_5919_ = crate::leanh::lean_ctor_get(v_t_5914_, 4);
                    v_isSharedCheck_6200_ = (!crate::leanh::lean_is_exclusive(v_t_5914_)) as u8;
                    if v_isSharedCheck_6200_ == 0 {
                        v___x_5921_ = v_t_5914_;
                        v_isShared_5922_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_5919_);
                        crate::leanh::lean_inc(v_l_5918_);
                        crate::leanh::lean_inc(v_v_5917_);
                        crate::leanh::lean_inc(v_k_5916_);
                        crate::leanh::lean_inc(v_size_5915_);
                        crate::leanh::lean_dec(v_t_5914_);
                        v___x_5921_ = crate::leanh::lean_box(0);
                        v_isShared_5922_ = v_isSharedCheck_6200_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6201_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6202_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6202_, 0, v___x_6201_);
                    crate::leanh::lean_ctor_set(v___x_6202_, 1, v_k_5912_);
                    crate::leanh::lean_ctor_set(v___x_6202_, 2, v_v_5913_);
                    crate::leanh::lean_ctor_set(v___x_6202_, 3, v_t_5914_);
                    crate::leanh::lean_ctor_set(v___x_6202_, 4, v_t_5914_);
                    return v___x_6202_;
                }
            }
            1 => {
                v___x_5923_ = lean_nat_dec_lt(v_k_5912_, v_k_5916_);
                if v___x_5923_ == 0 {
                    v___x_5924_ = lean_nat_dec_eq(v_k_5912_, v_k_5916_);
                    if v___x_5924_ == 0 {
                        crate::leanh::lean_dec(v_size_5915_);
                        v_impl_5925_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_5912_, v_v_5913_, v_r_5919_);
                        v___x_5926_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_5918_) == 0 {
                            v_size_5927_ = crate::leanh::lean_ctor_get(v_l_5918_, 0);
                            v_size_5928_ = crate::leanh::lean_ctor_get(v_impl_5925_, 0);
                            crate::leanh::lean_inc(v_size_5928_);
                            v_k_5929_ = crate::leanh::lean_ctor_get(v_impl_5925_, 1);
                            crate::leanh::lean_inc(v_k_5929_);
                            v_v_5930_ = crate::leanh::lean_ctor_get(v_impl_5925_, 2);
                            crate::leanh::lean_inc(v_v_5930_);
                            v_l_5931_ = crate::leanh::lean_ctor_get(v_impl_5925_, 3);
                            crate::leanh::lean_inc(v_l_5931_);
                            v_r_5932_ = crate::leanh::lean_ctor_get(v_impl_5925_, 4);
                            crate::leanh::lean_inc(v_r_5932_);
                            v___x_5933_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_5934_ = lean_nat_mul(v___x_5933_, v_size_5927_);
                            v___x_5935_ = lean_nat_dec_lt(v___x_5934_, v_size_5928_);
                            crate::leanh::lean_dec(v___x_5934_);
                            if v___x_5935_ == 0 {
                                crate::leanh::lean_dec(v_r_5932_);
                                crate::leanh::lean_dec(v_l_5931_);
                                crate::leanh::lean_dec(v_v_5930_);
                                crate::leanh::lean_dec(v_k_5929_);
                                v___x_5936_ = lean_nat_add(v___x_5926_, v_size_5927_);
                                v___x_5937_ = lean_nat_add(v___x_5936_, v_size_5928_);
                                crate::leanh::lean_dec(v_size_5928_);
                                crate::leanh::lean_dec(v___x_5936_);
                                if v_isShared_5922_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v_impl_5925_);
                                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_5937_);
                                    v___x_5939_ = v___x_5921_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5940_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5940_,
                                        0,
                                        v___x_5937_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5940_,
                                        1,
                                        v_k_5916_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5940_,
                                        2,
                                        v_v_5917_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5940_,
                                        3,
                                        v_l_5918_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5940_,
                                        4,
                                        v_impl_5925_,
                                    );
                                    v___x_5939_ = v_reuseFailAlloc_5940_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_6004_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_5925_)) as u8;
                                if v_isSharedCheck_6004_ == 0 {
                                    v_unused_6005_ = crate::leanh::lean_ctor_get(v_impl_5925_, 4);
                                    crate::leanh::lean_dec(v_unused_6005_);
                                    v_unused_6006_ = crate::leanh::lean_ctor_get(v_impl_5925_, 3);
                                    crate::leanh::lean_dec(v_unused_6006_);
                                    v_unused_6007_ = crate::leanh::lean_ctor_get(v_impl_5925_, 2);
                                    crate::leanh::lean_dec(v_unused_6007_);
                                    v_unused_6008_ = crate::leanh::lean_ctor_get(v_impl_5925_, 1);
                                    crate::leanh::lean_dec(v_unused_6008_);
                                    v_unused_6009_ = crate::leanh::lean_ctor_get(v_impl_5925_, 0);
                                    crate::leanh::lean_dec(v_unused_6009_);
                                    v___x_5942_ = v_impl_5925_;
                                    v_isShared_5943_ = v_isSharedCheck_6004_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_5925_);
                                    v___x_5942_ = crate::leanh::lean_box(0);
                                    v_isShared_5943_ = v_isSharedCheck_6004_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_6010_ = crate::leanh::lean_ctor_get(v_impl_5925_, 3);
                            crate::leanh::lean_inc(v_l_6010_);
                            if crate::leanh::lean_obj_tag(v_l_6010_) == 0 {
                                v_r_6011_ = crate::leanh::lean_ctor_get(v_impl_5925_, 4);
                                v_k_6012_ = crate::leanh::lean_ctor_get(v_impl_5925_, 1);
                                v_v_6013_ = crate::leanh::lean_ctor_get(v_impl_5925_, 2);
                                v_isSharedCheck_6036_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_5925_)) as u8;
                                if v_isSharedCheck_6036_ == 0 {
                                    v_unused_6037_ = crate::leanh::lean_ctor_get(v_impl_5925_, 3);
                                    crate::leanh::lean_dec(v_unused_6037_);
                                    v_unused_6038_ = crate::leanh::lean_ctor_get(v_impl_5925_, 0);
                                    crate::leanh::lean_dec(v_unused_6038_);
                                    v___x_6015_ = v_impl_5925_;
                                    v_isShared_6016_ = v_isSharedCheck_6036_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_6011_);
                                    crate::leanh::lean_inc(v_v_6013_);
                                    crate::leanh::lean_inc(v_k_6012_);
                                    crate::leanh::lean_dec(v_impl_5925_);
                                    v___x_6015_ = crate::leanh::lean_box(0);
                                    v_isShared_6016_ = v_isSharedCheck_6036_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_6039_ = crate::leanh::lean_ctor_get(v_impl_5925_, 4);
                                crate::leanh::lean_inc(v_r_6039_);
                                if crate::leanh::lean_obj_tag(v_r_6039_) == 0 {
                                    v_k_6040_ = crate::leanh::lean_ctor_get(v_impl_5925_, 1);
                                    v_v_6041_ = crate::leanh::lean_ctor_get(v_impl_5925_, 2);
                                    v_isSharedCheck_6052_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_5925_)) as u8;
                                    if v_isSharedCheck_6052_ == 0 {
                                        v_unused_6053_ =
                                            crate::leanh::lean_ctor_get(v_impl_5925_, 4);
                                        crate::leanh::lean_dec(v_unused_6053_);
                                        v_unused_6054_ =
                                            crate::leanh::lean_ctor_get(v_impl_5925_, 3);
                                        crate::leanh::lean_dec(v_unused_6054_);
                                        v_unused_6055_ =
                                            crate::leanh::lean_ctor_get(v_impl_5925_, 0);
                                        crate::leanh::lean_dec(v_unused_6055_);
                                        v___x_6043_ = v_impl_5925_;
                                        v_isShared_6044_ = v_isSharedCheck_6052_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_6041_);
                                        crate::leanh::lean_inc(v_k_6040_);
                                        crate::leanh::lean_dec(v_impl_5925_);
                                        v___x_6043_ = crate::leanh::lean_box(0);
                                        v_isShared_6044_ = v_isSharedCheck_6052_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_6056_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_5922_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_5921_, 4, v_impl_5925_);
                                        crate::leanh::lean_ctor_set(v___x_5921_, 3, v_r_6039_);
                                        crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6056_);
                                        v___x_6058_ = v___x_5921_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6059_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6059_,
                                            0,
                                            v___x_6056_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6059_,
                                            1,
                                            v_k_5916_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6059_,
                                            2,
                                            v_v_5917_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6059_,
                                            3,
                                            v_r_6039_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6059_,
                                            4,
                                            v_impl_5925_,
                                        );
                                        v___x_6058_ = v_reuseFailAlloc_6059_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_v_5917_);
                        crate::leanh::lean_dec(v_k_5916_);
                        if v_isShared_5922_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5921_, 2, v_v_5913_);
                            crate::leanh::lean_ctor_set(v___x_5921_, 1, v_k_5912_);
                            v___x_6061_ = v___x_5921_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_6062_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_size_5915_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 1, v_k_5912_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 2, v_v_5913_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 3, v_l_5918_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 4, v_r_5919_);
                            v___x_6061_ = v_reuseFailAlloc_6062_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_size_5915_);
                    v_impl_6063_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(v_k_5912_, v_v_5913_, v_l_5918_);
                    v___x_6064_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_r_5919_) == 0 {
                        v_size_6065_ = crate::leanh::lean_ctor_get(v_r_5919_, 0);
                        v_size_6066_ = crate::leanh::lean_ctor_get(v_impl_6063_, 0);
                        crate::leanh::lean_inc(v_size_6066_);
                        v_k_6067_ = crate::leanh::lean_ctor_get(v_impl_6063_, 1);
                        crate::leanh::lean_inc(v_k_6067_);
                        v_v_6068_ = crate::leanh::lean_ctor_get(v_impl_6063_, 2);
                        crate::leanh::lean_inc(v_v_6068_);
                        v_l_6069_ = crate::leanh::lean_ctor_get(v_impl_6063_, 3);
                        crate::leanh::lean_inc(v_l_6069_);
                        v_r_6070_ = crate::leanh::lean_ctor_get(v_impl_6063_, 4);
                        crate::leanh::lean_inc(v_r_6070_);
                        v___x_6071_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_6072_ = lean_nat_mul(v___x_6071_, v_size_6065_);
                        v___x_6073_ = lean_nat_dec_lt(v___x_6072_, v_size_6066_);
                        crate::leanh::lean_dec(v___x_6072_);
                        if v___x_6073_ == 0 {
                            crate::leanh::lean_dec(v_r_6070_);
                            crate::leanh::lean_dec(v_l_6069_);
                            crate::leanh::lean_dec(v_v_6068_);
                            crate::leanh::lean_dec(v_k_6067_);
                            v___x_6074_ = lean_nat_add(v___x_6064_, v_size_6066_);
                            crate::leanh::lean_dec(v_size_6066_);
                            v___x_6075_ = lean_nat_add(v___x_6074_, v_size_6065_);
                            crate::leanh::lean_dec(v___x_6074_);
                            if v_isShared_5922_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5921_, 3, v_impl_6063_);
                                crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6075_);
                                v___x_6077_ = v___x_5921_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_6078_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6075_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 1, v_k_5916_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 2, v_v_5917_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_6078_,
                                    3,
                                    v_impl_6063_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 4, v_r_5919_);
                                v___x_6077_ = v_reuseFailAlloc_6078_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_6144_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_6063_)) as u8;
                            if v_isSharedCheck_6144_ == 0 {
                                v_unused_6145_ = crate::leanh::lean_ctor_get(v_impl_6063_, 4);
                                crate::leanh::lean_dec(v_unused_6145_);
                                v_unused_6146_ = crate::leanh::lean_ctor_get(v_impl_6063_, 3);
                                crate::leanh::lean_dec(v_unused_6146_);
                                v_unused_6147_ = crate::leanh::lean_ctor_get(v_impl_6063_, 2);
                                crate::leanh::lean_dec(v_unused_6147_);
                                v_unused_6148_ = crate::leanh::lean_ctor_get(v_impl_6063_, 1);
                                crate::leanh::lean_dec(v_unused_6148_);
                                v_unused_6149_ = crate::leanh::lean_ctor_get(v_impl_6063_, 0);
                                crate::leanh::lean_dec(v_unused_6149_);
                                v___x_6080_ = v_impl_6063_;
                                v_isShared_6081_ = v_isSharedCheck_6144_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_impl_6063_);
                                v___x_6080_ = crate::leanh::lean_box(0);
                                v_isShared_6081_ = v_isSharedCheck_6144_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_6150_ = crate::leanh::lean_ctor_get(v_impl_6063_, 3);
                        crate::leanh::lean_inc(v_l_6150_);
                        if crate::leanh::lean_obj_tag(v_l_6150_) == 0 {
                            v_r_6151_ = crate::leanh::lean_ctor_get(v_impl_6063_, 4);
                            v_k_6152_ = crate::leanh::lean_ctor_get(v_impl_6063_, 1);
                            v_v_6153_ = crate::leanh::lean_ctor_get(v_impl_6063_, 2);
                            v_isSharedCheck_6164_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_6063_)) as u8;
                            if v_isSharedCheck_6164_ == 0 {
                                v_unused_6165_ = crate::leanh::lean_ctor_get(v_impl_6063_, 3);
                                crate::leanh::lean_dec(v_unused_6165_);
                                v_unused_6166_ = crate::leanh::lean_ctor_get(v_impl_6063_, 0);
                                crate::leanh::lean_dec(v_unused_6166_);
                                v___x_6155_ = v_impl_6063_;
                                v_isShared_6156_ = v_isSharedCheck_6164_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_r_6151_);
                                crate::leanh::lean_inc(v_v_6153_);
                                crate::leanh::lean_inc(v_k_6152_);
                                crate::leanh::lean_dec(v_impl_6063_);
                                v___x_6155_ = crate::leanh::lean_box(0);
                                v_isShared_6156_ = v_isSharedCheck_6164_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_6167_ = crate::leanh::lean_ctor_get(v_impl_6063_, 4);
                            crate::leanh::lean_inc(v_r_6167_);
                            if crate::leanh::lean_obj_tag(v_r_6167_) == 0 {
                                v_k_6168_ = crate::leanh::lean_ctor_get(v_impl_6063_, 1);
                                v_v_6169_ = crate::leanh::lean_ctor_get(v_impl_6063_, 2);
                                v_isSharedCheck_6192_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_6063_)) as u8;
                                if v_isSharedCheck_6192_ == 0 {
                                    v_unused_6193_ = crate::leanh::lean_ctor_get(v_impl_6063_, 4);
                                    crate::leanh::lean_dec(v_unused_6193_);
                                    v_unused_6194_ = crate::leanh::lean_ctor_get(v_impl_6063_, 3);
                                    crate::leanh::lean_dec(v_unused_6194_);
                                    v_unused_6195_ = crate::leanh::lean_ctor_get(v_impl_6063_, 0);
                                    crate::leanh::lean_dec(v_unused_6195_);
                                    v___x_6171_ = v_impl_6063_;
                                    v_isShared_6172_ = v_isSharedCheck_6192_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_6169_);
                                    crate::leanh::lean_inc(v_k_6168_);
                                    crate::leanh::lean_dec(v_impl_6063_);
                                    v___x_6171_ = crate::leanh::lean_box(0);
                                    v_isShared_6172_ = v_isSharedCheck_6192_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_6196_ = crate::leanh::lean_unsigned_to_nat(2);
                                if v_isShared_5922_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v_r_6167_);
                                    crate::leanh::lean_ctor_set(v___x_5921_, 3, v_impl_6063_);
                                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6196_);
                                    v___x_6198_ = v___x_5921_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6199_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6199_,
                                        0,
                                        v___x_6196_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6199_,
                                        1,
                                        v_k_5916_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6199_,
                                        2,
                                        v_v_5917_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6199_,
                                        3,
                                        v_impl_6063_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6199_,
                                        4,
                                        v_r_6167_,
                                    );
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
                v_size_5944_ = crate::leanh::lean_ctor_get(v_l_5931_, 0);
                v_k_5945_ = crate::leanh::lean_ctor_get(v_l_5931_, 1);
                v_v_5946_ = crate::leanh::lean_ctor_get(v_l_5931_, 2);
                v_l_5947_ = crate::leanh::lean_ctor_get(v_l_5931_, 3);
                v_r_5948_ = crate::leanh::lean_ctor_get(v_l_5931_, 4);
                v_size_5949_ = crate::leanh::lean_ctor_get(v_r_5932_, 0);
                v___x_5950_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5951_ = lean_nat_mul(v___x_5950_, v_size_5949_);
                v___x_5952_ = lean_nat_dec_lt(v_size_5944_, v___x_5951_);
                crate::leanh::lean_dec(v___x_5951_);
                if v___x_5952_ == 0 {
                    crate::leanh::lean_inc(v_r_5948_);
                    crate::leanh::lean_inc(v_l_5947_);
                    crate::leanh::lean_inc(v_v_5946_);
                    crate::leanh::lean_inc(v_k_5945_);
                    v_isSharedCheck_5980_ = (!crate::leanh::lean_is_exclusive(v_l_5931_)) as u8;
                    if v_isSharedCheck_5980_ == 0 {
                        v_unused_5981_ = crate::leanh::lean_ctor_get(v_l_5931_, 4);
                        crate::leanh::lean_dec(v_unused_5981_);
                        v_unused_5982_ = crate::leanh::lean_ctor_get(v_l_5931_, 3);
                        crate::leanh::lean_dec(v_unused_5982_);
                        v_unused_5983_ = crate::leanh::lean_ctor_get(v_l_5931_, 2);
                        crate::leanh::lean_dec(v_unused_5983_);
                        v_unused_5984_ = crate::leanh::lean_ctor_get(v_l_5931_, 1);
                        crate::leanh::lean_dec(v_unused_5984_);
                        v_unused_5985_ = crate::leanh::lean_ctor_get(v_l_5931_, 0);
                        crate::leanh::lean_dec(v_unused_5985_);
                        v___x_5954_ = v_l_5931_;
                        v_isShared_5955_ = v_isSharedCheck_5980_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_5931_);
                        v___x_5954_ = crate::leanh::lean_box(0);
                        v_isShared_5955_ = v_isSharedCheck_5980_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5921_);
                    v___x_5986_ = lean_nat_add(v___x_5926_, v_size_5927_);
                    v___x_5987_ = lean_nat_add(v___x_5986_, v_size_5928_);
                    crate::leanh::lean_dec(v_size_5928_);
                    v___x_5988_ = lean_nat_add(v___x_5986_, v_size_5944_);
                    crate::leanh::lean_dec(v___x_5986_);
                    crate::leanh::lean_inc_ref(v_l_5918_);
                    if v_isShared_5943_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5942_, 4, v_l_5931_);
                        crate::leanh::lean_ctor_set(v___x_5942_, 3, v_l_5918_);
                        crate::leanh::lean_ctor_set(v___x_5942_, 2, v_v_5917_);
                        crate::leanh::lean_ctor_set(v___x_5942_, 1, v_k_5916_);
                        crate::leanh::lean_ctor_set(v___x_5942_, 0, v___x_5988_);
                        v___x_5990_ = v___x_5942_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6003_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6003_, 0, v___x_5988_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6003_, 1, v_k_5916_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6003_, 2, v_v_5917_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6003_, 3, v_l_5918_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6003_, 4, v_l_5931_);
                        v___x_5990_ = v_reuseFailAlloc_6003_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5956_ = lean_nat_add(v___x_5926_, v_size_5927_);
                v___x_5957_ = lean_nat_add(v___x_5956_, v_size_5928_);
                crate::leanh::lean_dec(v_size_5928_);
                if crate::leanh::lean_obj_tag(v_l_5947_) == 0 {
                    v_size_5978_ = crate::leanh::lean_ctor_get(v_l_5947_, 0);
                    crate::leanh::lean_inc(v_size_5978_);
                    v___y_5970_ = v_size_5978_;
                    state = 8;
                    continue;
                } else {
                    v___x_5979_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5970_ = v___x_5979_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_5962_ = lean_nat_add(v___y_5960_, v___y_5961_);
                crate::leanh::lean_dec(v___y_5961_);
                crate::leanh::lean_dec(v___y_5960_);
                if v_isShared_5955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5954_, 4, v_r_5932_);
                    crate::leanh::lean_ctor_set(v___x_5954_, 3, v_r_5948_);
                    crate::leanh::lean_ctor_set(v___x_5954_, 2, v_v_5930_);
                    crate::leanh::lean_ctor_set(v___x_5954_, 1, v_k_5929_);
                    crate::leanh::lean_ctor_set(v___x_5954_, 0, v___x_5962_);
                    v___x_5964_ = v___x_5954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5968_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5968_, 0, v___x_5962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5968_, 1, v_k_5929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5968_, 2, v_v_5930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5968_, 3, v_r_5948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5968_, 4, v_r_5932_);
                    v___x_5964_ = v_reuseFailAlloc_5968_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5942_, 4, v___x_5964_);
                    crate::leanh::lean_ctor_set(v___x_5942_, 3, v___y_5959_);
                    crate::leanh::lean_ctor_set(v___x_5942_, 2, v_v_5946_);
                    crate::leanh::lean_ctor_set(v___x_5942_, 1, v_k_5945_);
                    crate::leanh::lean_ctor_set(v___x_5942_, 0, v___x_5957_);
                    v___x_5966_ = v___x_5942_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5967_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5967_, 0, v___x_5957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5967_, 1, v_k_5945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5967_, 2, v_v_5946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5967_, 3, v___y_5959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5967_, 4, v___x_5964_);
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
                crate::leanh::lean_dec(v___y_5970_);
                crate::leanh::lean_dec(v___x_5956_);
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v_l_5947_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_5971_);
                    v___x_5973_ = v___x_5921_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5977_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5977_, 0, v___x_5971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5977_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5977_, 3, v_l_5918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5977_, 4, v_l_5947_);
                    v___x_5973_ = v_reuseFailAlloc_5977_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5974_ = lean_nat_add(v___x_5926_, v_size_5949_);
                if crate::leanh::lean_obj_tag(v_r_5948_) == 0 {
                    v_size_5975_ = crate::leanh::lean_ctor_get(v_r_5948_, 0);
                    crate::leanh::lean_inc(v_size_5975_);
                    v___y_5959_ = v___x_5973_;
                    v___y_5960_ = v___x_5974_;
                    v___y_5961_ = v_size_5975_;
                    state = 5;
                    continue;
                } else {
                    v___x_5976_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5959_ = v___x_5973_;
                    v___y_5960_ = v___x_5974_;
                    v___y_5961_ = v___x_5976_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_5997_ = (!crate::leanh::lean_is_exclusive(v_l_5918_)) as u8;
                if v_isSharedCheck_5997_ == 0 {
                    v_unused_5998_ = crate::leanh::lean_ctor_get(v_l_5918_, 4);
                    crate::leanh::lean_dec(v_unused_5998_);
                    v_unused_5999_ = crate::leanh::lean_ctor_get(v_l_5918_, 3);
                    crate::leanh::lean_dec(v_unused_5999_);
                    v_unused_6000_ = crate::leanh::lean_ctor_get(v_l_5918_, 2);
                    crate::leanh::lean_dec(v_unused_6000_);
                    v_unused_6001_ = crate::leanh::lean_ctor_get(v_l_5918_, 1);
                    crate::leanh::lean_dec(v_unused_6001_);
                    v_unused_6002_ = crate::leanh::lean_ctor_get(v_l_5918_, 0);
                    crate::leanh::lean_dec(v_unused_6002_);
                    v___x_5992_ = v_l_5918_;
                    v_isShared_5993_ = v_isSharedCheck_5997_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_5918_);
                    v___x_5992_ = crate::leanh::lean_box(0);
                    v_isShared_5993_ = v_isSharedCheck_5997_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5993_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5992_, 4, v_r_5932_);
                    crate::leanh::lean_ctor_set(v___x_5992_, 3, v___x_5990_);
                    crate::leanh::lean_ctor_set(v___x_5992_, 2, v_v_5930_);
                    crate::leanh::lean_ctor_set(v___x_5992_, 1, v_k_5929_);
                    crate::leanh::lean_ctor_set(v___x_5992_, 0, v___x_5987_);
                    v___x_5995_ = v___x_5992_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5996_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5996_, 0, v___x_5987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5996_, 1, v_k_5929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_v_5930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5996_, 3, v___x_5990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5996_, 4, v_r_5932_);
                    v___x_5995_ = v_reuseFailAlloc_5996_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5995_;
            }
            13 => {
                v_k_6017_ = crate::leanh::lean_ctor_get(v_l_6010_, 1);
                v_v_6018_ = crate::leanh::lean_ctor_get(v_l_6010_, 2);
                v_isSharedCheck_6032_ = (!crate::leanh::lean_is_exclusive(v_l_6010_)) as u8;
                if v_isSharedCheck_6032_ == 0 {
                    v_unused_6033_ = crate::leanh::lean_ctor_get(v_l_6010_, 4);
                    crate::leanh::lean_dec(v_unused_6033_);
                    v_unused_6034_ = crate::leanh::lean_ctor_get(v_l_6010_, 3);
                    crate::leanh::lean_dec(v_unused_6034_);
                    v_unused_6035_ = crate::leanh::lean_ctor_get(v_l_6010_, 0);
                    crate::leanh::lean_dec(v_unused_6035_);
                    v___x_6020_ = v_l_6010_;
                    v_isShared_6021_ = v_isSharedCheck_6032_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_6018_);
                    crate::leanh::lean_inc(v_k_6017_);
                    crate::leanh::lean_dec(v_l_6010_);
                    v___x_6020_ = crate::leanh::lean_box(0);
                    v_isShared_6021_ = v_isSharedCheck_6032_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_6022_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_6011_, 2);
                if v_isShared_6021_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6020_, 4, v_r_6011_);
                    crate::leanh::lean_ctor_set(v___x_6020_, 3, v_r_6011_);
                    crate::leanh::lean_ctor_set(v___x_6020_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v___x_6020_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v___x_6020_, 0, v___x_5926_);
                    v___x_6024_ = v___x_6020_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6031_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_5926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 3, v_r_6011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6031_, 4, v_r_6011_);
                    v___x_6024_ = v_reuseFailAlloc_6031_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_r_6011_);
                if v_isShared_6016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6015_, 3, v_r_6011_);
                    crate::leanh::lean_ctor_set(v___x_6015_, 0, v___x_5926_);
                    v___x_6026_ = v___x_6015_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6030_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 0, v___x_5926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 1, v_k_6012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 2, v_v_6013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 3, v_r_6011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 4, v_r_6011_);
                    v___x_6026_ = v_reuseFailAlloc_6030_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v___x_6026_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 3, v___x_6024_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 2, v_v_6018_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 1, v_k_6017_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6022_);
                    v___x_6028_ = v___x_5921_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6029_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 0, v___x_6022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 1, v_k_6017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 2, v_v_6018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 3, v___x_6024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 4, v___x_6026_);
                    v___x_6028_ = v_reuseFailAlloc_6029_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6028_;
            }
            18 => {
                v___x_6045_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_6044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6043_, 4, v_l_6010_);
                    crate::leanh::lean_ctor_set(v___x_6043_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v___x_6043_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v___x_6043_, 0, v___x_5926_);
                    v___x_6047_ = v___x_6043_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6051_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 0, v___x_5926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 3, v_l_6010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 4, v_l_6010_);
                    v___x_6047_ = v_reuseFailAlloc_6051_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v_r_6039_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 3, v___x_6047_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 2, v_v_6041_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 1, v_k_6040_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6045_);
                    v___x_6049_ = v___x_5921_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6050_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6050_, 0, v___x_6045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6050_, 1, v_k_6040_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6050_, 2, v_v_6041_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6050_, 3, v___x_6047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6050_, 4, v_r_6039_);
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
                v_size_6082_ = crate::leanh::lean_ctor_get(v_l_6069_, 0);
                v_size_6083_ = crate::leanh::lean_ctor_get(v_r_6070_, 0);
                v_k_6084_ = crate::leanh::lean_ctor_get(v_r_6070_, 1);
                v_v_6085_ = crate::leanh::lean_ctor_get(v_r_6070_, 2);
                v_l_6086_ = crate::leanh::lean_ctor_get(v_r_6070_, 3);
                v_r_6087_ = crate::leanh::lean_ctor_get(v_r_6070_, 4);
                v___x_6088_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6089_ = lean_nat_mul(v___x_6088_, v_size_6082_);
                v___x_6090_ = lean_nat_dec_lt(v_size_6083_, v___x_6089_);
                crate::leanh::lean_dec(v___x_6089_);
                if v___x_6090_ == 0 {
                    crate::leanh::lean_inc(v_r_6087_);
                    crate::leanh::lean_inc(v_l_6086_);
                    crate::leanh::lean_inc(v_v_6085_);
                    crate::leanh::lean_inc(v_k_6084_);
                    v_isSharedCheck_6119_ = (!crate::leanh::lean_is_exclusive(v_r_6070_)) as u8;
                    if v_isSharedCheck_6119_ == 0 {
                        v_unused_6120_ = crate::leanh::lean_ctor_get(v_r_6070_, 4);
                        crate::leanh::lean_dec(v_unused_6120_);
                        v_unused_6121_ = crate::leanh::lean_ctor_get(v_r_6070_, 3);
                        crate::leanh::lean_dec(v_unused_6121_);
                        v_unused_6122_ = crate::leanh::lean_ctor_get(v_r_6070_, 2);
                        crate::leanh::lean_dec(v_unused_6122_);
                        v_unused_6123_ = crate::leanh::lean_ctor_get(v_r_6070_, 1);
                        crate::leanh::lean_dec(v_unused_6123_);
                        v_unused_6124_ = crate::leanh::lean_ctor_get(v_r_6070_, 0);
                        crate::leanh::lean_dec(v_unused_6124_);
                        v___x_6092_ = v_r_6070_;
                        v_isShared_6093_ = v_isSharedCheck_6119_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_6070_);
                        v___x_6092_ = crate::leanh::lean_box(0);
                        v_isShared_6093_ = v_isSharedCheck_6119_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5921_);
                    v___x_6125_ = lean_nat_add(v___x_6064_, v_size_6066_);
                    crate::leanh::lean_dec(v_size_6066_);
                    v___x_6126_ = lean_nat_add(v___x_6125_, v_size_6065_);
                    crate::leanh::lean_dec(v___x_6125_);
                    v___x_6127_ = lean_nat_add(v___x_6064_, v_size_6065_);
                    v___x_6128_ = lean_nat_add(v___x_6127_, v_size_6083_);
                    crate::leanh::lean_dec(v___x_6127_);
                    crate::leanh::lean_inc_ref(v_r_5919_);
                    if v_isShared_6081_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6080_, 4, v_r_5919_);
                        crate::leanh::lean_ctor_set(v___x_6080_, 3, v_r_6070_);
                        crate::leanh::lean_ctor_set(v___x_6080_, 2, v_v_5917_);
                        crate::leanh::lean_ctor_set(v___x_6080_, 1, v_k_5916_);
                        crate::leanh::lean_ctor_set(v___x_6080_, 0, v___x_6128_);
                        v___x_6130_ = v___x_6080_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_6143_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 0, v___x_6128_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 1, v_k_5916_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 2, v_v_5917_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 3, v_r_6070_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6143_, 4, v_r_5919_);
                        v___x_6130_ = v_reuseFailAlloc_6143_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_6094_ = lean_nat_add(v___x_6064_, v_size_6066_);
                crate::leanh::lean_dec(v_size_6066_);
                v___x_6095_ = lean_nat_add(v___x_6094_, v_size_6065_);
                crate::leanh::lean_dec(v___x_6094_);
                v___x_6107_ = lean_nat_add(v___x_6064_, v_size_6082_);
                if crate::leanh::lean_obj_tag(v_l_6086_) == 0 {
                    v_size_6117_ = crate::leanh::lean_ctor_get(v_l_6086_, 0);
                    crate::leanh::lean_inc(v_size_6117_);
                    v___y_6109_ = v_size_6117_;
                    state = 29;
                    continue;
                } else {
                    v___x_6118_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6109_ = v___x_6118_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_6100_ = lean_nat_add(v___y_6098_, v___y_6099_);
                crate::leanh::lean_dec(v___y_6099_);
                crate::leanh::lean_dec(v___y_6098_);
                if v_isShared_6093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6092_, 4, v_r_5919_);
                    crate::leanh::lean_ctor_set(v___x_6092_, 3, v_r_6087_);
                    crate::leanh::lean_ctor_set(v___x_6092_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v___x_6092_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v___x_6092_, 0, v___x_6100_);
                    v___x_6102_ = v___x_6092_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6106_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6106_, 0, v___x_6100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6106_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6106_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6106_, 3, v_r_6087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6106_, 4, v_r_5919_);
                    v___x_6102_ = v_reuseFailAlloc_6106_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_6081_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6080_, 4, v___x_6102_);
                    crate::leanh::lean_ctor_set(v___x_6080_, 3, v___y_6097_);
                    crate::leanh::lean_ctor_set(v___x_6080_, 2, v_v_6085_);
                    crate::leanh::lean_ctor_set(v___x_6080_, 1, v_k_6084_);
                    crate::leanh::lean_ctor_set(v___x_6080_, 0, v___x_6095_);
                    v___x_6104_ = v___x_6080_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6105_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 0, v___x_6095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 1, v_k_6084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 2, v_v_6085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 3, v___y_6097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 4, v___x_6102_);
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
                crate::leanh::lean_dec(v___y_6109_);
                crate::leanh::lean_dec(v___x_6107_);
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v_l_6086_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 3, v_l_6069_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 2, v_v_6068_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 1, v_k_6067_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6110_);
                    v___x_6112_ = v___x_5921_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 0, v___x_6110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 1, v_k_6067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 2, v_v_6068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 3, v_l_6069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 4, v_l_6086_);
                    v___x_6112_ = v_reuseFailAlloc_6116_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_6113_ = lean_nat_add(v___x_6064_, v_size_6065_);
                if crate::leanh::lean_obj_tag(v_r_6087_) == 0 {
                    v_size_6114_ = crate::leanh::lean_ctor_get(v_r_6087_, 0);
                    crate::leanh::lean_inc(v_size_6114_);
                    v___y_6097_ = v___x_6112_;
                    v___y_6098_ = v___x_6113_;
                    v___y_6099_ = v_size_6114_;
                    state = 26;
                    continue;
                } else {
                    v___x_6115_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6097_ = v___x_6112_;
                    v___y_6098_ = v___x_6113_;
                    v___y_6099_ = v___x_6115_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_6137_ = (!crate::leanh::lean_is_exclusive(v_r_5919_)) as u8;
                if v_isSharedCheck_6137_ == 0 {
                    v_unused_6138_ = crate::leanh::lean_ctor_get(v_r_5919_, 4);
                    crate::leanh::lean_dec(v_unused_6138_);
                    v_unused_6139_ = crate::leanh::lean_ctor_get(v_r_5919_, 3);
                    crate::leanh::lean_dec(v_unused_6139_);
                    v_unused_6140_ = crate::leanh::lean_ctor_get(v_r_5919_, 2);
                    crate::leanh::lean_dec(v_unused_6140_);
                    v_unused_6141_ = crate::leanh::lean_ctor_get(v_r_5919_, 1);
                    crate::leanh::lean_dec(v_unused_6141_);
                    v_unused_6142_ = crate::leanh::lean_ctor_get(v_r_5919_, 0);
                    crate::leanh::lean_dec(v_unused_6142_);
                    v___x_6132_ = v_r_5919_;
                    v_isShared_6133_ = v_isSharedCheck_6137_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_5919_);
                    v___x_6132_ = crate::leanh::lean_box(0);
                    v_isShared_6133_ = v_isSharedCheck_6137_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_6133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6132_, 4, v___x_6130_);
                    crate::leanh::lean_ctor_set(v___x_6132_, 3, v_l_6069_);
                    crate::leanh::lean_ctor_set(v___x_6132_, 2, v_v_6068_);
                    crate::leanh::lean_ctor_set(v___x_6132_, 1, v_k_6067_);
                    crate::leanh::lean_ctor_set(v___x_6132_, 0, v___x_6126_);
                    v___x_6135_ = v___x_6132_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6136_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6136_, 0, v___x_6126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6136_, 1, v_k_6067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6136_, 2, v_v_6068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6136_, 3, v_l_6069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6136_, 4, v___x_6130_);
                    v___x_6135_ = v_reuseFailAlloc_6136_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6135_;
            }
            34 => {
                v___x_6157_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_6151_);
                if v_isShared_6156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6155_, 3, v_r_6151_);
                    crate::leanh::lean_ctor_set(v___x_6155_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v___x_6155_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v___x_6155_, 0, v___x_6064_);
                    v___x_6159_ = v___x_6155_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6163_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 0, v___x_6064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 3, v_r_6151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 4, v_r_6151_);
                    v___x_6159_ = v_reuseFailAlloc_6163_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v___x_6159_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 3, v_l_6150_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 2, v_v_6153_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 1, v_k_6152_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6157_);
                    v___x_6161_ = v___x_5921_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6162_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 0, v___x_6157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 1, v_k_6152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 2, v_v_6153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 3, v_l_6150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6162_, 4, v___x_6159_);
                    v___x_6161_ = v_reuseFailAlloc_6162_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_6161_;
            }
            37 => {
                v_k_6173_ = crate::leanh::lean_ctor_get(v_r_6167_, 1);
                v_v_6174_ = crate::leanh::lean_ctor_get(v_r_6167_, 2);
                v_isSharedCheck_6188_ = (!crate::leanh::lean_is_exclusive(v_r_6167_)) as u8;
                if v_isSharedCheck_6188_ == 0 {
                    v_unused_6189_ = crate::leanh::lean_ctor_get(v_r_6167_, 4);
                    crate::leanh::lean_dec(v_unused_6189_);
                    v_unused_6190_ = crate::leanh::lean_ctor_get(v_r_6167_, 3);
                    crate::leanh::lean_dec(v_unused_6190_);
                    v_unused_6191_ = crate::leanh::lean_ctor_get(v_r_6167_, 0);
                    crate::leanh::lean_dec(v_unused_6191_);
                    v___x_6176_ = v_r_6167_;
                    v_isShared_6177_ = v_isSharedCheck_6188_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_6174_);
                    crate::leanh::lean_inc(v_k_6173_);
                    crate::leanh::lean_dec(v_r_6167_);
                    v___x_6176_ = crate::leanh::lean_box(0);
                    v_isShared_6177_ = v_isSharedCheck_6188_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_6178_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_6177_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6176_, 4, v_l_6150_);
                    crate::leanh::lean_ctor_set(v___x_6176_, 3, v_l_6150_);
                    crate::leanh::lean_ctor_set(v___x_6176_, 2, v_v_6169_);
                    crate::leanh::lean_ctor_set(v___x_6176_, 1, v_k_6168_);
                    crate::leanh::lean_ctor_set(v___x_6176_, 0, v___x_6064_);
                    v___x_6180_ = v___x_6176_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6187_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6187_, 0, v___x_6064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6187_, 1, v_k_6168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6187_, 2, v_v_6169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6187_, 3, v_l_6150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6187_, 4, v_l_6150_);
                    v___x_6180_ = v_reuseFailAlloc_6187_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_6172_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6171_, 4, v_l_6150_);
                    crate::leanh::lean_ctor_set(v___x_6171_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v___x_6171_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v___x_6171_, 0, v___x_6064_);
                    v___x_6182_ = v___x_6171_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6186_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 0, v___x_6064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 1, v_k_5916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 2, v_v_5917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 3, v_l_6150_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 4, v_l_6150_);
                    v___x_6182_ = v_reuseFailAlloc_6186_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_5922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5921_, 4, v___x_6182_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 3, v___x_6180_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 2, v_v_6174_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 1, v_k_6173_);
                    crate::leanh::lean_ctor_set(v___x_5921_, 0, v___x_6178_);
                    v___x_6184_ = v___x_5921_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6185_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6185_, 0, v___x_6178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6185_, 1, v_k_6173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6185_, 2, v_v_6174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6185_, 3, v___x_6180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6185_, 4, v___x_6182_);
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
    mut v_k_6203_: *mut crate::leanh::LeanObject,
    mut v_t_6204_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: u8 = 0;
    let mut v___x_6209_: u8 = 0;
    let mut v___x_6212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_6204_) == 0 {
                    v_k_6205_ = crate::leanh::lean_ctor_get(v_t_6204_, 1);
                    v_l_6206_ = crate::leanh::lean_ctor_get(v_t_6204_, 3);
                    v_r_6207_ = crate::leanh::lean_ctor_get(v_t_6204_, 4);
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
    mut v_k_6213_: *mut crate::leanh::LeanObject,
    mut v_t_6214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6215_: u8 = 0;
    let mut v_r_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6215_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
            v_k_6213_, v_t_6214_,
        );
    crate::leanh::lean_dec(v_t_6214_);
    crate::leanh::lean_dec(v_k_6213_);
    v_r_6216_ = crate::leanh::lean_box((v_res_6215_) as usize);
    return v_r_6216_;
}
pub unsafe fn l_Lean_IR_mkIndexSet(
    mut v_idx_6217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: u8 = 0;
    v___x_6218_ = crate::leanh::lean_box(1);
    v___x_6219_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
            v_idx_6217_,
            v___x_6218_,
        );
    if v___x_6219_ == 0 {
        let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6220_ = crate::leanh::lean_box(0);
        v___x_6221_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
                v_idx_6217_,
                v___x_6220_,
                v___x_6218_,
            );
        return v___x_6221_;
    } else {
        crate::leanh::lean_dec(v_idx_6217_);
        return v___x_6218_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(
    mut v_00_u03b2_6222_: *mut crate::leanh::LeanObject,
    mut v_k_6223_: *mut crate::leanh::LeanObject,
    mut v_t_6224_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6225_: u8 = 0;
    v___x_6225_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___redArg(
            v_k_6223_, v_t_6224_,
        );
    return v___x_6225_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0___boxed(
    mut v_00_u03b2_6226_: *mut crate::leanh::LeanObject,
    mut v_k_6227_: *mut crate::leanh::LeanObject,
    mut v_t_6228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6229_: u8 = 0;
    let mut v_r_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6229_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_IR_mkIndexSet_spec__0(
        v_00_u03b2_6226_,
        v_k_6227_,
        v_t_6228_,
    );
    crate::leanh::lean_dec(v_t_6228_);
    crate::leanh::lean_dec(v_k_6227_);
    v_r_6230_ = crate::leanh::lean_box((v_res_6229_) as usize);
    return v_r_6230_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1(
    mut v_00_u03b2_6231_: *mut crate::leanh::LeanObject,
    mut v_k_6232_: *mut crate::leanh::LeanObject,
    mut v_v_6233_: *mut crate::leanh::LeanObject,
    mut v_t_6234_: *mut crate::leanh::LeanObject,
    mut v_hl_6235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6236_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_k_6232_, v_v_6233_, v_t_6234_,
    );
    return v___x_6236_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorIdx(
    mut v_x_6237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_6237_) {
        0 => {
            let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6238_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_6238_;
        }
        1 => {
            let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6239_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_6239_;
        }
        _ => {
            let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6240_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_6240_;
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorIdx___boxed(
    mut v_x_6241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6242_ = l_Lean_IR_LocalContextEntry_ctorIdx(v_x_6241_);
    crate::leanh::lean_dec_ref(v_x_6241_);
    return v_res_6242_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorElim___redArg(
    mut v_t_6243_: *mut crate::leanh::LeanObject,
    mut v_k_6244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_6243_) {
        0 => {
            let mut v_a_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6245_ = crate::leanh::lean_ctor_get(v_t_6243_, 0);
            crate::leanh::lean_inc(v_a_6245_);
            crate::leanh::lean_dec_ref_known(v_t_6243_, 1);
            v___x_6246_ = crate::leanh::lean_apply_1(v_k_6244_, v_a_6245_);
            return v___x_6246_;
        }
        1 => {
            let mut v_a_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6247_ = crate::leanh::lean_ctor_get(v_t_6243_, 0);
            crate::leanh::lean_inc(v_a_6247_);
            v_a_6248_ = crate::leanh::lean_ctor_get(v_t_6243_, 1);
            crate::leanh::lean_inc_ref(v_a_6248_);
            crate::leanh::lean_dec_ref_known(v_t_6243_, 2);
            v___x_6249_ = crate::leanh::lean_apply_2(v_k_6244_, v_a_6247_, v_a_6248_);
            return v___x_6249_;
        }
        _ => {
            let mut v_a_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_6250_ = crate::leanh::lean_ctor_get(v_t_6243_, 0);
            crate::leanh::lean_inc_ref(v_a_6250_);
            v_a_6251_ = crate::leanh::lean_ctor_get(v_t_6243_, 1);
            crate::leanh::lean_inc(v_a_6251_);
            crate::leanh::lean_dec_ref_known(v_t_6243_, 2);
            v___x_6252_ = crate::leanh::lean_apply_2(v_k_6244_, v_a_6250_, v_a_6251_);
            return v___x_6252_;
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorElim(
    mut v_motive_6253_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_6254_: *mut crate::leanh::LeanObject,
    mut v_t_6255_: *mut crate::leanh::LeanObject,
    mut v_h_6256_: *mut crate::leanh::LeanObject,
    mut v_k_6257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6255_, v_k_6257_);
    return v___x_6258_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_ctorElim___boxed(
    mut v_motive_6259_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_6260_: *mut crate::leanh::LeanObject,
    mut v_t_6261_: *mut crate::leanh::LeanObject,
    mut v_h_6262_: *mut crate::leanh::LeanObject,
    mut v_k_6263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6264_ = l_Lean_IR_LocalContextEntry_ctorElim(
        v_motive_6259_,
        v_ctorIdx_6260_,
        v_t_6261_,
        v_h_6262_,
        v_k_6263_,
    );
    crate::leanh::lean_dec(v_ctorIdx_6260_);
    return v_res_6264_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_param_elim___redArg(
    mut v_t_6265_: *mut crate::leanh::LeanObject,
    mut v_param_6266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6267_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6265_, v_param_6266_);
    return v___x_6267_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_param_elim(
    mut v_motive_6268_: *mut crate::leanh::LeanObject,
    mut v_t_6269_: *mut crate::leanh::LeanObject,
    mut v_h_6270_: *mut crate::leanh::LeanObject,
    mut v_param_6271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6272_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6269_, v_param_6271_);
    return v___x_6272_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_localVar_elim___redArg(
    mut v_t_6273_: *mut crate::leanh::LeanObject,
    mut v_localVar_6274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6275_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6273_, v_localVar_6274_);
    return v___x_6275_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_localVar_elim(
    mut v_motive_6276_: *mut crate::leanh::LeanObject,
    mut v_t_6277_: *mut crate::leanh::LeanObject,
    mut v_h_6278_: *mut crate::leanh::LeanObject,
    mut v_localVar_6279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6280_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6277_, v_localVar_6279_);
    return v___x_6280_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_joinPoint_elim___redArg(
    mut v_t_6281_: *mut crate::leanh::LeanObject,
    mut v_joinPoint_6282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6283_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6281_, v_joinPoint_6282_);
    return v___x_6283_;
}
pub unsafe fn l_Lean_IR_LocalContextEntry_joinPoint_elim(
    mut v_motive_6284_: *mut crate::leanh::LeanObject,
    mut v_t_6285_: *mut crate::leanh::LeanObject,
    mut v_h_6286_: *mut crate::leanh::LeanObject,
    mut v_joinPoint_6287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = l_Lean_IR_LocalContextEntry_ctorElim___redArg(v_t_6285_, v_joinPoint_6287_);
    return v___x_6288_;
}
pub unsafe fn l_Lean_IR_LocalContext_addLocal(
    mut v_ctx_6289_: *mut crate::leanh::LeanObject,
    mut v_x_6290_: *mut crate::leanh::LeanObject,
    mut v_t_6291_: *mut crate::leanh::LeanObject,
    mut v_v_6292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6293_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6293_, 0, v_t_6291_);
    crate::leanh::lean_ctor_set(v___x_6293_, 1, v_v_6292_);
    v___x_6294_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_x_6290_,
        v___x_6293_,
        v_ctx_6289_,
    );
    return v___x_6294_;
}
pub unsafe fn l_Lean_IR_LocalContext_addJP(
    mut v_ctx_6295_: *mut crate::leanh::LeanObject,
    mut v_j_6296_: *mut crate::leanh::LeanObject,
    mut v_xs_6297_: *mut crate::leanh::LeanObject,
    mut v_b_6298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6299_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6299_, 0, v_xs_6297_);
    crate::leanh::lean_ctor_set(v___x_6299_, 1, v_b_6298_);
    v___x_6300_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_j_6296_,
        v___x_6299_,
        v_ctx_6295_,
    );
    return v___x_6300_;
}
pub unsafe fn l_Lean_IR_LocalContext_addParam(
    mut v_ctx_6301_: *mut crate::leanh::LeanObject,
    mut v_p_6302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6303_ = crate::leanh::lean_ctor_get(v_p_6302_, 0);
    crate::leanh::lean_inc(v_x_6303_);
    v_ty_6304_ = crate::leanh::lean_ctor_get(v_p_6302_, 1);
    crate::leanh::lean_inc(v_ty_6304_);
    crate::leanh::lean_dec_ref(v_p_6302_);
    v___x_6305_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6305_, 0, v_ty_6304_);
    v___x_6306_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
        v_x_6303_,
        v___x_6305_,
        v_ctx_6301_,
    );
    return v___x_6306_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(
    mut v_as_6307_: *mut crate::leanh::LeanObject,
    mut v_i_6308_: usize,
    mut v_stop_6309_: usize,
    mut v_b_6310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6311_: u8 = 0;
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: usize = 0;
    let mut v___x_6315_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6311_ = lean_usize_dec_eq(v_i_6308_, v_stop_6309_);
                if v___x_6311_ == 0 {
                    v___x_6312_ = lean_array_uget_borrowed(v_as_6307_, v_i_6308_);
                    crate::leanh::lean_inc(v___x_6312_);
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
    mut v_as_6317_: *mut crate::leanh::LeanObject,
    mut v_i_6318_: *mut crate::leanh::LeanObject,
    mut v_stop_6319_: *mut crate::leanh::LeanObject,
    mut v_b_6320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_6321_: usize = 0;
    let mut v_stop_boxed_6322_: usize = 0;
    let mut v_res_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6321_ = crate::leanh::lean_unbox_usize(v_i_6318_);
    crate::leanh::lean_dec(v_i_6318_);
    v_stop_boxed_6322_ = crate::leanh::lean_unbox_usize(v_stop_6319_);
    crate::leanh::lean_dec(v_stop_6319_);
    v_res_6323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_as_6317_, v_i_boxed_6321_, v_stop_boxed_6322_, v_b_6320_);
    crate::leanh::lean_dec_ref(v_as_6317_);
    return v_res_6323_;
}
pub unsafe fn l_Lean_IR_LocalContext_addParams(
    mut v_ctx_6324_: *mut crate::leanh::LeanObject,
    mut v_ps_6325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: u8 = 0;
    v___x_6326_ = crate::leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_6330_ = 0usize;
                v___x_6331_ = lean_usize_of_nat(v___x_6327_);
                v___x_6332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_6325_, v___x_6330_, v___x_6331_, v_ctx_6324_);
                return v___x_6332_;
            }
        } else {
            let mut v___x_6333_: usize = 0;
            let mut v___x_6334_: usize = 0;
            let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_6333_ = 0usize;
            v___x_6334_ = lean_usize_of_nat(v___x_6327_);
            v___x_6335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_IR_LocalContext_addParams_spec__0(v_ps_6325_, v___x_6333_, v___x_6334_, v_ctx_6324_);
            return v___x_6335_;
        }
    }
}
pub unsafe fn l_Lean_IR_LocalContext_addParams___boxed(
    mut v_ctx_6336_: *mut crate::leanh::LeanObject,
    mut v_ps_6337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6338_ = l_Lean_IR_LocalContext_addParams(v_ctx_6336_, v_ps_6337_);
    crate::leanh::lean_dec_ref(v_ps_6337_);
    return v_res_6338_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(
    mut v_t_6339_: *mut crate::leanh::LeanObject,
    mut v_k_6340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: u8 = 0;
    let mut v___x_6346_: u8 = 0;
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_6339_) == 0 {
                    v_k_6341_ = crate::leanh::lean_ctor_get(v_t_6339_, 1);
                    v_v_6342_ = crate::leanh::lean_ctor_get(v_t_6339_, 2);
                    v_l_6343_ = crate::leanh::lean_ctor_get(v_t_6339_, 3);
                    v_r_6344_ = crate::leanh::lean_ctor_get(v_t_6339_, 4);
                    v___x_6345_ = lean_nat_dec_lt(v_k_6340_, v_k_6341_);
                    if v___x_6345_ == 0 {
                        v___x_6346_ = lean_nat_dec_eq(v_k_6340_, v_k_6341_);
                        if v___x_6346_ == 0 {
                            v_t_6339_ = v_r_6344_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_6342_);
                            v___x_6348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6348_, 0, v_v_6342_);
                            return v___x_6348_;
                        }
                    } else {
                        v_t_6339_ = v_l_6343_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_6350_ = crate::leanh::lean_box(0);
                    return v___x_6350_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(
    mut v_t_6351_: *mut crate::leanh::LeanObject,
    mut v_k_6352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6353_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_6351_, v_k_6352_);
    crate::leanh::lean_dec(v_k_6352_);
    crate::leanh::lean_dec(v_t_6351_);
    return v_res_6353_;
}
pub unsafe fn l_Lean_IR_LocalContext_isJP(
    mut v_ctx_6354_: *mut crate::leanh::LeanObject,
    mut v_idx_6355_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6356_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6354_, v_idx_6355_);
    if crate::leanh::lean_obj_tag(v___x_6356_) == 1 {
        let mut v_val_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6357_ = crate::leanh::lean_ctor_get(v___x_6356_, 0);
        crate::leanh::lean_inc(v_val_6357_);
        crate::leanh::lean_dec_ref_known(v___x_6356_, 1);
        if crate::leanh::lean_obj_tag(v_val_6357_) == 2 {
            let mut v___x_6358_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_val_6357_, 2);
            v___x_6358_ = 1;
            return v___x_6358_;
        } else {
            let mut v___x_6359_: u8 = 0;
            crate::leanh::lean_dec(v_val_6357_);
            v___x_6359_ = 0;
            return v___x_6359_;
        }
    } else {
        let mut v___x_6360_: u8 = 0;
        crate::leanh::lean_dec(v___x_6356_);
        v___x_6360_ = 0;
        return v___x_6360_;
    }
}
pub unsafe fn l_Lean_IR_LocalContext_isJP___boxed(
    mut v_ctx_6361_: *mut crate::leanh::LeanObject,
    mut v_idx_6362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6363_: u8 = 0;
    let mut v_r_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6363_ = l_Lean_IR_LocalContext_isJP(v_ctx_6361_, v_idx_6362_);
    crate::leanh::lean_dec(v_idx_6362_);
    crate::leanh::lean_dec(v_ctx_6361_);
    v_r_6364_ = crate::leanh::lean_box((v_res_6363_) as usize);
    return v_r_6364_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(
    mut v_00_u03b4_6365_: *mut crate::leanh::LeanObject,
    mut v_t_6366_: *mut crate::leanh::LeanObject,
    mut v_k_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6368_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_t_6366_, v_k_6367_);
    return v___x_6368_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___boxed(
    mut v_00_u03b4_6369_: *mut crate::leanh::LeanObject,
    mut v_t_6370_: *mut crate::leanh::LeanObject,
    mut v_k_6371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6372_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0(
            v_00_u03b4_6369_,
            v_t_6370_,
            v_k_6371_,
        );
    crate::leanh::lean_dec(v_k_6371_);
    crate::leanh::lean_dec(v_t_6370_);
    return v_res_6372_;
}
pub unsafe fn l_Lean_IR_LocalContext_getJPBody(
    mut v_ctx_6373_: *mut crate::leanh::LeanObject,
    mut v_j_6374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6379_: u8 = 0;
    let mut v_a_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6385_: u8 = 0;
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6375_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6373_, v_j_6374_);
                if crate::leanh::lean_obj_tag(v___x_6375_) == 1 {
                    v_val_6376_ = crate::leanh::lean_ctor_get(v___x_6375_, 0);
                    v_isSharedCheck_6385_ = (!crate::leanh::lean_is_exclusive(v___x_6375_)) as u8;
                    if v_isSharedCheck_6385_ == 0 {
                        v___x_6378_ = v___x_6375_;
                        v_isShared_6379_ = v_isSharedCheck_6385_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6376_);
                        crate::leanh::lean_dec(v___x_6375_);
                        v___x_6378_ = crate::leanh::lean_box(0);
                        v_isShared_6379_ = v_isSharedCheck_6385_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6375_);
                    v___x_6386_ = crate::leanh::lean_box(0);
                    return v___x_6386_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_6376_) == 2 {
                    v_a_6380_ = crate::leanh::lean_ctor_get(v_val_6376_, 1);
                    crate::leanh::lean_inc(v_a_6380_);
                    crate::leanh::lean_dec_ref_known(v_val_6376_, 2);
                    if v_isShared_6379_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6378_, 0, v_a_6380_);
                        v___x_6382_ = v___x_6378_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_a_6380_);
                        v___x_6382_ = v_reuseFailAlloc_6383_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6378_);
                    crate::leanh::lean_dec(v_val_6376_);
                    v___x_6384_ = crate::leanh::lean_box(0);
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
    mut v_ctx_6387_: *mut crate::leanh::LeanObject,
    mut v_j_6388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6389_ = l_Lean_IR_LocalContext_getJPBody(v_ctx_6387_, v_j_6388_);
    crate::leanh::lean_dec(v_j_6388_);
    crate::leanh::lean_dec(v_ctx_6387_);
    return v_res_6389_;
}
pub unsafe fn l_Lean_IR_LocalContext_getJPParams(
    mut v_ctx_6390_: *mut crate::leanh::LeanObject,
    mut v_j_6391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6396_: u8 = 0;
    let mut v_a_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6402_: u8 = 0;
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6392_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6390_, v_j_6391_);
                if crate::leanh::lean_obj_tag(v___x_6392_) == 1 {
                    v_val_6393_ = crate::leanh::lean_ctor_get(v___x_6392_, 0);
                    v_isSharedCheck_6402_ = (!crate::leanh::lean_is_exclusive(v___x_6392_)) as u8;
                    if v_isSharedCheck_6402_ == 0 {
                        v___x_6395_ = v___x_6392_;
                        v_isShared_6396_ = v_isSharedCheck_6402_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6393_);
                        crate::leanh::lean_dec(v___x_6392_);
                        v___x_6395_ = crate::leanh::lean_box(0);
                        v_isShared_6396_ = v_isSharedCheck_6402_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6392_);
                    v___x_6403_ = crate::leanh::lean_box(0);
                    return v___x_6403_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_6393_) == 2 {
                    v_a_6397_ = crate::leanh::lean_ctor_get(v_val_6393_, 0);
                    crate::leanh::lean_inc_ref(v_a_6397_);
                    crate::leanh::lean_dec_ref_known(v_val_6393_, 2);
                    if v_isShared_6396_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6395_, 0, v_a_6397_);
                        v___x_6399_ = v___x_6395_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6400_, 0, v_a_6397_);
                        v___x_6399_ = v_reuseFailAlloc_6400_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6395_);
                    crate::leanh::lean_dec(v_val_6393_);
                    v___x_6401_ = crate::leanh::lean_box(0);
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
    mut v_ctx_6404_: *mut crate::leanh::LeanObject,
    mut v_j_6405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6406_ = l_Lean_IR_LocalContext_getJPParams(v_ctx_6404_, v_j_6405_);
    crate::leanh::lean_dec(v_j_6405_);
    crate::leanh::lean_dec(v_ctx_6404_);
    return v_res_6406_;
}
pub unsafe fn l_Lean_IR_LocalContext_isParam(
    mut v_ctx_6407_: *mut crate::leanh::LeanObject,
    mut v_idx_6408_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6409_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6407_, v_idx_6408_);
    if crate::leanh::lean_obj_tag(v___x_6409_) == 1 {
        let mut v_val_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6410_ = crate::leanh::lean_ctor_get(v___x_6409_, 0);
        crate::leanh::lean_inc(v_val_6410_);
        crate::leanh::lean_dec_ref_known(v___x_6409_, 1);
        if crate::leanh::lean_obj_tag(v_val_6410_) == 0 {
            let mut v___x_6411_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_val_6410_, 1);
            v___x_6411_ = 1;
            return v___x_6411_;
        } else {
            let mut v___x_6412_: u8 = 0;
            crate::leanh::lean_dec(v_val_6410_);
            v___x_6412_ = 0;
            return v___x_6412_;
        }
    } else {
        let mut v___x_6413_: u8 = 0;
        crate::leanh::lean_dec(v___x_6409_);
        v___x_6413_ = 0;
        return v___x_6413_;
    }
}
pub unsafe fn l_Lean_IR_LocalContext_isParam___boxed(
    mut v_ctx_6414_: *mut crate::leanh::LeanObject,
    mut v_idx_6415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6416_: u8 = 0;
    let mut v_r_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6416_ = l_Lean_IR_LocalContext_isParam(v_ctx_6414_, v_idx_6415_);
    crate::leanh::lean_dec(v_idx_6415_);
    crate::leanh::lean_dec(v_ctx_6414_);
    v_r_6417_ = crate::leanh::lean_box((v_res_6416_) as usize);
    return v_r_6417_;
}
pub unsafe fn l_Lean_IR_LocalContext_isLocalVar(
    mut v_ctx_6418_: *mut crate::leanh::LeanObject,
    mut v_idx_6419_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6420_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_6418_, v_idx_6419_);
    if crate::leanh::lean_obj_tag(v___x_6420_) == 1 {
        let mut v_val_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6421_ = crate::leanh::lean_ctor_get(v___x_6420_, 0);
        crate::leanh::lean_inc(v_val_6421_);
        crate::leanh::lean_dec_ref_known(v___x_6420_, 1);
        if crate::leanh::lean_obj_tag(v_val_6421_) == 1 {
            let mut v___x_6422_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_val_6421_, 2);
            v___x_6422_ = 1;
            return v___x_6422_;
        } else {
            let mut v___x_6423_: u8 = 0;
            crate::leanh::lean_dec(v_val_6421_);
            v___x_6423_ = 0;
            return v___x_6423_;
        }
    } else {
        let mut v___x_6424_: u8 = 0;
        crate::leanh::lean_dec(v___x_6420_);
        v___x_6424_ = 0;
        return v___x_6424_;
    }
}
pub unsafe fn l_Lean_IR_LocalContext_isLocalVar___boxed(
    mut v_ctx_6425_: *mut crate::leanh::LeanObject,
    mut v_idx_6426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6427_: u8 = 0;
    let mut v_r_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6427_ = l_Lean_IR_LocalContext_isLocalVar(v_ctx_6425_, v_idx_6426_);
    crate::leanh::lean_dec(v_idx_6426_);
    crate::leanh::lean_dec(v_ctx_6425_);
    v_r_6428_ = crate::leanh::lean_box((v_res_6427_) as usize);
    return v_r_6428_;
}
pub unsafe fn l_Lean_IR_LocalContext_contains(
    mut v_ctx_6429_: *mut crate::leanh::LeanObject,
    mut v_idx_6430_: *mut crate::leanh::LeanObject,
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
    mut v_ctx_6432_: *mut crate::leanh::LeanObject,
    mut v_idx_6433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6434_: u8 = 0;
    let mut v_r_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6434_ = l_Lean_IR_LocalContext_contains(v_ctx_6432_, v_idx_6433_);
    crate::leanh::lean_dec(v_idx_6433_);
    crate::leanh::lean_dec(v_ctx_6432_);
    v_r_6435_ = crate::leanh::lean_box((v_res_6434_) as usize);
    return v_r_6435_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(
    mut v_k_6436_: *mut crate::leanh::LeanObject,
    mut v_t_6437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6444_: u8 = 0;
    let mut v___x_6445_: u8 = 0;
    let mut v___x_6446_: u8 = 0;
    let mut v_impl_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: u8 = 0;
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6465_: u8 = 0;
    let mut v_size_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: u8 = 0;
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6477_: u8 = 0;
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6503_: u8 = 0;
    let mut v_unused_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6517_: u8 = 0;
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6521_: u8 = 0;
    let mut v_unused_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_unused_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6546_: u8 = 0;
    let mut v_size_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6556_: u8 = 0;
    let mut v_unused_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6563_: u8 = 0;
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6571_: u8 = 0;
    let mut v_unused_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v_k_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6585_: u8 = 0;
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6596_: u8 = 0;
    let mut v_unused_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6600_: u8 = 0;
    let mut v_unused_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: u8 = 0;
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6625_: u8 = 0;
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: u8 = 0;
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6641_: u8 = 0;
    let mut v_size_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: u8 = 0;
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6653_: u8 = 0;
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6678_: u8 = 0;
    let mut v_unused_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6693_: u8 = 0;
    let mut v_unused_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6701_: u8 = 0;
    let mut v_k_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6719_: u8 = 0;
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6730_: u8 = 0;
    let mut v_unused_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6752_: u8 = 0;
    let mut v_unused_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_unused_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6766_: u8 = 0;
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: u8 = 0;
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v_size_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: u8 = 0;
    let mut v___x_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6794_: u8 = 0;
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6806_: u8 = 0;
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6810_: u8 = 0;
    let mut v_unused_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6829_: u8 = 0;
    let mut v_unused_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6845_: u8 = 0;
    let mut v_unused_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6853_: u8 = 0;
    let mut v_k_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6874_: u8 = 0;
    let mut v_unused_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6882_: u8 = 0;
    let mut v_k_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6889_: u8 = 0;
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6900_: u8 = 0;
    let mut v_unused_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v_unused_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6916_: u8 = 0;
    let mut v_unused_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: u8 = 0;
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6940_: u8 = 0;
    let mut v_size_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6952_: u8 = 0;
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6977_: u8 = 0;
    let mut v_unused_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6990_: u8 = 0;
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6994_: u8 = 0;
    let mut v_unused_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7001_: u8 = 0;
    let mut v_unused_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7019_: u8 = 0;
    let mut v_size_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7029_: u8 = 0;
    let mut v_unused_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7036_: u8 = 0;
    let mut v_k_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7041_: u8 = 0;
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7052_: u8 = 0;
    let mut v_unused_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7056_: u8 = 0;
    let mut v_unused_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7065_: u8 = 0;
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7073_: u8 = 0;
    let mut v_unused_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7082_: u8 = 0;
    let mut v___x_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7090_: u8 = 0;
    let mut v_unused_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7096_: u8 = 0;
    let mut v_unused_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_6437_) == 0 {
                    v_k_6438_ = crate::leanh::lean_ctor_get(v_t_6437_, 1);
                    v_v_6439_ = crate::leanh::lean_ctor_get(v_t_6437_, 2);
                    v_l_6440_ = crate::leanh::lean_ctor_get(v_t_6437_, 3);
                    v_r_6441_ = crate::leanh::lean_ctor_get(v_t_6437_, 4);
                    v_isSharedCheck_7096_ = (!crate::leanh::lean_is_exclusive(v_t_6437_)) as u8;
                    if v_isSharedCheck_7096_ == 0 {
                        v_unused_7097_ = crate::leanh::lean_ctor_get(v_t_6437_, 0);
                        crate::leanh::lean_dec(v_unused_7097_);
                        v___x_6443_ = v_t_6437_;
                        v_isShared_6444_ = v_isSharedCheck_7096_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_6441_);
                        crate::leanh::lean_inc(v_l_6440_);
                        crate::leanh::lean_inc(v_v_6439_);
                        crate::leanh::lean_inc(v_k_6438_);
                        crate::leanh::lean_dec(v_t_6437_);
                        v___x_6443_ = crate::leanh::lean_box(0);
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
                        v___x_6448_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_6447_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_6440_) == 0 {
                                v_size_6449_ = crate::leanh::lean_ctor_get(v_impl_6447_, 0);
                                crate::leanh::lean_inc(v_size_6449_);
                                v_size_6450_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                v_k_6451_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                v_v_6452_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                v_l_6453_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                v_r_6454_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                crate::leanh::lean_inc(v_r_6454_);
                                v___x_6455_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_6456_ = lean_nat_mul(v___x_6455_, v_size_6449_);
                                v___x_6457_ = lean_nat_dec_lt(v___x_6456_, v_size_6450_);
                                crate::leanh::lean_dec(v___x_6456_);
                                if v___x_6457_ == 0 {
                                    crate::leanh::lean_dec(v_r_6454_);
                                    v___x_6458_ = lean_nat_add(v___x_6448_, v_size_6450_);
                                    v___x_6459_ = lean_nat_add(v___x_6458_, v_size_6449_);
                                    crate::leanh::lean_dec(v_size_6449_);
                                    crate::leanh::lean_dec(v___x_6458_);
                                    if v_isShared_6444_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_6443_, 4, v_impl_6447_);
                                        crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6459_);
                                        v___x_6461_ = v___x_6443_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6462_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6462_,
                                            0,
                                            v___x_6459_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6462_,
                                            1,
                                            v_k_6438_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6462_,
                                            2,
                                            v_v_6439_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6462_,
                                            3,
                                            v_l_6440_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6462_,
                                            4,
                                            v_impl_6447_,
                                        );
                                        v___x_6461_ = v_reuseFailAlloc_6462_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_6453_);
                                    crate::leanh::lean_inc(v_v_6452_);
                                    crate::leanh::lean_inc(v_k_6451_);
                                    crate::leanh::lean_inc(v_size_6450_);
                                    v_isSharedCheck_6528_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                                    if v_isSharedCheck_6528_ == 0 {
                                        v_unused_6529_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                        crate::leanh::lean_dec(v_unused_6529_);
                                        v_unused_6530_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                        crate::leanh::lean_dec(v_unused_6530_);
                                        v_unused_6531_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                        crate::leanh::lean_dec(v_unused_6531_);
                                        v_unused_6532_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                        crate::leanh::lean_dec(v_unused_6532_);
                                        v_unused_6533_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                        crate::leanh::lean_dec(v_unused_6533_);
                                        v___x_6464_ = v_l_6440_;
                                        v_isShared_6465_ = v_isSharedCheck_6528_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_6440_);
                                        v___x_6464_ = crate::leanh::lean_box(0);
                                        v_isShared_6465_ = v_isSharedCheck_6528_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_6534_ = crate::leanh::lean_ctor_get(v_impl_6447_, 0);
                                crate::leanh::lean_inc(v_size_6534_);
                                v___x_6535_ = lean_nat_add(v___x_6448_, v_size_6534_);
                                crate::leanh::lean_dec(v_size_6534_);
                                if v_isShared_6444_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v_impl_6447_);
                                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6535_);
                                    v___x_6537_ = v___x_6443_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6538_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6538_,
                                        0,
                                        v___x_6535_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6538_,
                                        1,
                                        v_k_6438_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6538_,
                                        2,
                                        v_v_6439_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6538_,
                                        3,
                                        v_l_6440_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6538_,
                                        4,
                                        v_impl_6447_,
                                    );
                                    v___x_6537_ = v_reuseFailAlloc_6538_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_l_6440_) == 0 {
                                v_l_6539_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                if crate::leanh::lean_obj_tag(v_l_6539_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_6539_);
                                    v_r_6540_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                    crate::leanh::lean_inc(v_r_6540_);
                                    if crate::leanh::lean_obj_tag(v_r_6540_) == 0 {
                                        v_size_6541_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                        v_k_6542_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                        v_v_6543_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                        v_isSharedCheck_6556_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                                        if v_isSharedCheck_6556_ == 0 {
                                            v_unused_6557_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                            crate::leanh::lean_dec(v_unused_6557_);
                                            v_unused_6558_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                            crate::leanh::lean_dec(v_unused_6558_);
                                            v___x_6545_ = v_l_6440_;
                                            v_isShared_6546_ = v_isSharedCheck_6556_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_6543_);
                                            crate::leanh::lean_inc(v_k_6542_);
                                            crate::leanh::lean_inc(v_size_6541_);
                                            crate::leanh::lean_dec(v_l_6440_);
                                            v___x_6545_ = crate::leanh::lean_box(0);
                                            v_isShared_6546_ = v_isSharedCheck_6556_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_6559_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                        v_v_6560_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                        v_isSharedCheck_6571_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                                        if v_isSharedCheck_6571_ == 0 {
                                            v_unused_6572_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                            crate::leanh::lean_dec(v_unused_6572_);
                                            v_unused_6573_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                            crate::leanh::lean_dec(v_unused_6573_);
                                            v_unused_6574_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                            crate::leanh::lean_dec(v_unused_6574_);
                                            v___x_6562_ = v_l_6440_;
                                            v_isShared_6563_ = v_isSharedCheck_6571_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_6560_);
                                            crate::leanh::lean_inc(v_k_6559_);
                                            crate::leanh::lean_dec(v_l_6440_);
                                            v___x_6562_ = crate::leanh::lean_box(0);
                                            v_isShared_6563_ = v_isSharedCheck_6571_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_6575_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                    crate::leanh::lean_inc(v_r_6575_);
                                    if crate::leanh::lean_obj_tag(v_r_6575_) == 0 {
                                        crate::leanh::lean_inc(v_l_6539_);
                                        v_k_6576_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                        v_v_6577_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                        v_isSharedCheck_6600_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                                        if v_isSharedCheck_6600_ == 0 {
                                            v_unused_6601_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                            crate::leanh::lean_dec(v_unused_6601_);
                                            v_unused_6602_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                            crate::leanh::lean_dec(v_unused_6602_);
                                            v_unused_6603_ =
                                                crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                            crate::leanh::lean_dec(v_unused_6603_);
                                            v___x_6579_ = v_l_6440_;
                                            v_isShared_6580_ = v_isSharedCheck_6600_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_6577_);
                                            crate::leanh::lean_inc(v_k_6576_);
                                            crate::leanh::lean_dec(v_l_6440_);
                                            v___x_6579_ = crate::leanh::lean_box(0);
                                            v_isShared_6580_ = v_isSharedCheck_6600_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_6604_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_6444_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_6443_, 4, v_r_6575_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_6443_,
                                                0,
                                                v___x_6604_,
                                            );
                                            v___x_6606_ = v___x_6443_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_6607_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6607_,
                                                0,
                                                v___x_6604_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6607_,
                                                1,
                                                v_k_6438_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6607_,
                                                2,
                                                v_v_6439_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6607_,
                                                3,
                                                v_l_6440_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6607_,
                                                4,
                                                v_r_6575_,
                                            );
                                            v___x_6606_ = v_reuseFailAlloc_6607_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_6444_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v_l_6440_);
                                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6448_);
                                    v___x_6609_ = v___x_6443_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6610_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6610_,
                                        0,
                                        v___x_6448_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6610_,
                                        1,
                                        v_k_6438_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6610_,
                                        2,
                                        v_v_6439_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6610_,
                                        3,
                                        v_l_6440_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6610_,
                                        4,
                                        v_l_6440_,
                                    );
                                    v___x_6609_ = v_reuseFailAlloc_6610_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6443_);
                        crate::leanh::lean_dec(v_v_6439_);
                        crate::leanh::lean_dec(v_k_6438_);
                        if crate::leanh::lean_obj_tag(v_l_6440_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_6441_) == 0 {
                                v_size_6611_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                v_k_6612_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                v_v_6613_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                v_l_6614_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                v_r_6615_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                crate::leanh::lean_inc(v_r_6615_);
                                v_size_6616_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                                v_k_6617_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                                v_v_6618_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                                v_l_6619_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                                crate::leanh::lean_inc(v_l_6619_);
                                v_r_6620_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                v___x_6621_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_6622_ = lean_nat_dec_lt(v_size_6611_, v_size_6616_);
                                if v___x_6622_ == 0 {
                                    crate::leanh::lean_inc(v_l_6614_);
                                    crate::leanh::lean_inc(v_v_6613_);
                                    crate::leanh::lean_inc(v_k_6612_);
                                    v_isSharedCheck_6758_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                                    if v_isSharedCheck_6758_ == 0 {
                                        v_unused_6759_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                        crate::leanh::lean_dec(v_unused_6759_);
                                        v_unused_6760_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                        crate::leanh::lean_dec(v_unused_6760_);
                                        v_unused_6761_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                        crate::leanh::lean_dec(v_unused_6761_);
                                        v_unused_6762_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                        crate::leanh::lean_dec(v_unused_6762_);
                                        v_unused_6763_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                        crate::leanh::lean_dec(v_unused_6763_);
                                        v___x_6624_ = v_l_6440_;
                                        v_isShared_6625_ = v_isSharedCheck_6758_;
                                        state = 27;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_6440_);
                                        v___x_6624_ = crate::leanh::lean_box(0);
                                        v_isShared_6625_ = v_isSharedCheck_6758_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_6620_);
                                    crate::leanh::lean_inc(v_v_6618_);
                                    crate::leanh::lean_inc(v_k_6617_);
                                    v_isSharedCheck_6916_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_6916_ == 0 {
                                        v_unused_6917_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                        crate::leanh::lean_dec(v_unused_6917_);
                                        v_unused_6918_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                                        crate::leanh::lean_dec(v_unused_6918_);
                                        v_unused_6919_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                                        crate::leanh::lean_dec(v_unused_6919_);
                                        v_unused_6920_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                                        crate::leanh::lean_dec(v_unused_6920_);
                                        v_unused_6921_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                                        crate::leanh::lean_dec(v_unused_6921_);
                                        v___x_6765_ = v_r_6441_;
                                        v_isShared_6766_ = v_isSharedCheck_6916_;
                                        state = 49;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_6441_);
                                        v___x_6765_ = crate::leanh::lean_box(0);
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
                    v___x_6923_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_impl_6922_) == 0 {
                        if crate::leanh::lean_obj_tag(v_r_6441_) == 0 {
                            v_size_6924_ = crate::leanh::lean_ctor_get(v_impl_6922_, 0);
                            crate::leanh::lean_inc(v_size_6924_);
                            v_size_6925_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                            v_k_6926_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                            v_v_6927_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                            v_l_6928_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                            crate::leanh::lean_inc(v_l_6928_);
                            v_r_6929_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                            v___x_6930_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_6931_ = lean_nat_mul(v___x_6930_, v_size_6924_);
                            v___x_6932_ = lean_nat_dec_lt(v___x_6931_, v_size_6925_);
                            crate::leanh::lean_dec(v___x_6931_);
                            if v___x_6932_ == 0 {
                                crate::leanh::lean_dec(v_l_6928_);
                                v___x_6933_ = lean_nat_add(v___x_6923_, v_size_6924_);
                                crate::leanh::lean_dec(v_size_6924_);
                                v___x_6934_ = lean_nat_add(v___x_6933_, v_size_6925_);
                                crate::leanh::lean_dec(v___x_6933_);
                                if v_isShared_6444_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v_impl_6922_);
                                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6934_);
                                    v___x_6936_ = v___x_6443_;
                                    state = 72;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6937_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6937_,
                                        0,
                                        v___x_6934_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6937_,
                                        1,
                                        v_k_6438_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6937_,
                                        2,
                                        v_v_6439_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6937_,
                                        3,
                                        v_impl_6922_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6937_,
                                        4,
                                        v_r_6441_,
                                    );
                                    v___x_6936_ = v_reuseFailAlloc_6937_;
                                    state = 72;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc(v_r_6929_);
                                crate::leanh::lean_inc(v_v_6927_);
                                crate::leanh::lean_inc(v_k_6926_);
                                crate::leanh::lean_inc(v_size_6925_);
                                v_isSharedCheck_7001_ =
                                    (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                                if v_isSharedCheck_7001_ == 0 {
                                    v_unused_7002_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                    crate::leanh::lean_dec(v_unused_7002_);
                                    v_unused_7003_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                                    crate::leanh::lean_dec(v_unused_7003_);
                                    v_unused_7004_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                                    crate::leanh::lean_dec(v_unused_7004_);
                                    v_unused_7005_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                                    crate::leanh::lean_dec(v_unused_7005_);
                                    v_unused_7006_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                                    crate::leanh::lean_dec(v_unused_7006_);
                                    v___x_6939_ = v_r_6441_;
                                    v_isShared_6940_ = v_isSharedCheck_7001_;
                                    state = 73;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_r_6441_);
                                    v___x_6939_ = crate::leanh::lean_box(0);
                                    v_isShared_6940_ = v_isSharedCheck_7001_;
                                    state = 73;
                                    continue;
                                }
                            }
                        } else {
                            v_size_7007_ = crate::leanh::lean_ctor_get(v_impl_6922_, 0);
                            crate::leanh::lean_inc(v_size_7007_);
                            v___x_7008_ = lean_nat_add(v___x_6923_, v_size_7007_);
                            crate::leanh::lean_dec(v_size_7007_);
                            if v_isShared_6444_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6443_, 3, v_impl_6922_);
                                crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_7008_);
                                v___x_7010_ = v___x_6443_;
                                state = 83;
                                continue;
                            } else {
                                v_reuseFailAlloc_7011_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7011_, 0, v___x_7008_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7011_, 1, v_k_6438_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7011_, 2, v_v_6439_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_7011_,
                                    3,
                                    v_impl_6922_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7011_, 4, v_r_6441_);
                                v___x_7010_ = v_reuseFailAlloc_7011_;
                                state = 83;
                                continue;
                            }
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_6441_) == 0 {
                            v_l_7012_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                            crate::leanh::lean_inc(v_l_7012_);
                            if crate::leanh::lean_obj_tag(v_l_7012_) == 0 {
                                v_r_7013_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                crate::leanh::lean_inc(v_r_7013_);
                                if crate::leanh::lean_obj_tag(v_r_7013_) == 0 {
                                    v_size_7014_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                                    v_k_7015_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                                    v_v_7016_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7029_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7029_ == 0 {
                                        v_unused_7030_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                        crate::leanh::lean_dec(v_unused_7030_);
                                        v_unused_7031_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                                        crate::leanh::lean_dec(v_unused_7031_);
                                        v___x_7018_ = v_r_6441_;
                                        v_isShared_7019_ = v_isSharedCheck_7029_;
                                        state = 84;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_7016_);
                                        crate::leanh::lean_inc(v_k_7015_);
                                        crate::leanh::lean_inc(v_size_7014_);
                                        crate::leanh::lean_dec(v_r_6441_);
                                        v___x_7018_ = crate::leanh::lean_box(0);
                                        v_isShared_7019_ = v_isSharedCheck_7029_;
                                        state = 84;
                                        continue;
                                    }
                                } else {
                                    v_k_7032_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                                    v_v_7033_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7056_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7056_ == 0 {
                                        v_unused_7057_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                        crate::leanh::lean_dec(v_unused_7057_);
                                        v_unused_7058_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                                        crate::leanh::lean_dec(v_unused_7058_);
                                        v_unused_7059_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                                        crate::leanh::lean_dec(v_unused_7059_);
                                        v___x_7035_ = v_r_6441_;
                                        v_isShared_7036_ = v_isSharedCheck_7056_;
                                        state = 87;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_7033_);
                                        crate::leanh::lean_inc(v_k_7032_);
                                        crate::leanh::lean_dec(v_r_6441_);
                                        v___x_7035_ = crate::leanh::lean_box(0);
                                        v_isShared_7036_ = v_isSharedCheck_7056_;
                                        state = 87;
                                        continue;
                                    }
                                }
                            } else {
                                v_r_7060_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                crate::leanh::lean_inc(v_r_7060_);
                                if crate::leanh::lean_obj_tag(v_r_7060_) == 0 {
                                    v_k_7061_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                                    v_v_7062_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7073_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7073_ == 0 {
                                        v_unused_7074_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                        crate::leanh::lean_dec(v_unused_7074_);
                                        v_unused_7075_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                                        crate::leanh::lean_dec(v_unused_7075_);
                                        v_unused_7076_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                                        crate::leanh::lean_dec(v_unused_7076_);
                                        v___x_7064_ = v_r_6441_;
                                        v_isShared_7065_ = v_isSharedCheck_7073_;
                                        state = 92;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_7062_);
                                        crate::leanh::lean_inc(v_k_7061_);
                                        crate::leanh::lean_dec(v_r_6441_);
                                        v___x_7064_ = crate::leanh::lean_box(0);
                                        v_isShared_7065_ = v_isSharedCheck_7073_;
                                        state = 92;
                                        continue;
                                    }
                                } else {
                                    v_size_7077_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                                    v_k_7078_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                                    v_v_7079_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                                    v_isSharedCheck_7090_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                                    if v_isSharedCheck_7090_ == 0 {
                                        v_unused_7091_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                                        crate::leanh::lean_dec(v_unused_7091_);
                                        v_unused_7092_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                                        crate::leanh::lean_dec(v_unused_7092_);
                                        v___x_7081_ = v_r_6441_;
                                        v_isShared_7082_ = v_isSharedCheck_7090_;
                                        state = 95;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_7079_);
                                        crate::leanh::lean_inc(v_k_7078_);
                                        crate::leanh::lean_inc(v_size_7077_);
                                        crate::leanh::lean_dec(v_r_6441_);
                                        v___x_7081_ = crate::leanh::lean_box(0);
                                        v_isShared_7082_ = v_isSharedCheck_7090_;
                                        state = 95;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            if v_isShared_6444_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6443_, 3, v_r_6441_);
                                crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6923_);
                                v___x_7094_ = v___x_6443_;
                                state = 98;
                                continue;
                            } else {
                                v_reuseFailAlloc_7095_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 0, v___x_6923_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 1, v_k_6438_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 2, v_v_6439_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 3, v_r_6441_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 4, v_r_6441_);
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
                v_size_6466_ = crate::leanh::lean_ctor_get(v_l_6453_, 0);
                v_size_6467_ = crate::leanh::lean_ctor_get(v_r_6454_, 0);
                v_k_6468_ = crate::leanh::lean_ctor_get(v_r_6454_, 1);
                v_v_6469_ = crate::leanh::lean_ctor_get(v_r_6454_, 2);
                v_l_6470_ = crate::leanh::lean_ctor_get(v_r_6454_, 3);
                v_r_6471_ = crate::leanh::lean_ctor_get(v_r_6454_, 4);
                v___x_6472_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6473_ = lean_nat_mul(v___x_6472_, v_size_6466_);
                v___x_6474_ = lean_nat_dec_lt(v_size_6467_, v___x_6473_);
                crate::leanh::lean_dec(v___x_6473_);
                if v___x_6474_ == 0 {
                    crate::leanh::lean_inc(v_r_6471_);
                    crate::leanh::lean_inc(v_l_6470_);
                    crate::leanh::lean_inc(v_v_6469_);
                    crate::leanh::lean_inc(v_k_6468_);
                    v_isSharedCheck_6503_ = (!crate::leanh::lean_is_exclusive(v_r_6454_)) as u8;
                    if v_isSharedCheck_6503_ == 0 {
                        v_unused_6504_ = crate::leanh::lean_ctor_get(v_r_6454_, 4);
                        crate::leanh::lean_dec(v_unused_6504_);
                        v_unused_6505_ = crate::leanh::lean_ctor_get(v_r_6454_, 3);
                        crate::leanh::lean_dec(v_unused_6505_);
                        v_unused_6506_ = crate::leanh::lean_ctor_get(v_r_6454_, 2);
                        crate::leanh::lean_dec(v_unused_6506_);
                        v_unused_6507_ = crate::leanh::lean_ctor_get(v_r_6454_, 1);
                        crate::leanh::lean_dec(v_unused_6507_);
                        v_unused_6508_ = crate::leanh::lean_ctor_get(v_r_6454_, 0);
                        crate::leanh::lean_dec(v_unused_6508_);
                        v___x_6476_ = v_r_6454_;
                        v_isShared_6477_ = v_isSharedCheck_6503_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_6454_);
                        v___x_6476_ = crate::leanh::lean_box(0);
                        v_isShared_6477_ = v_isSharedCheck_6503_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6443_);
                    v___x_6509_ = lean_nat_add(v___x_6448_, v_size_6450_);
                    crate::leanh::lean_dec(v_size_6450_);
                    v___x_6510_ = lean_nat_add(v___x_6509_, v_size_6449_);
                    crate::leanh::lean_dec(v___x_6509_);
                    v___x_6511_ = lean_nat_add(v___x_6448_, v_size_6449_);
                    crate::leanh::lean_dec(v_size_6449_);
                    v___x_6512_ = lean_nat_add(v___x_6511_, v_size_6467_);
                    crate::leanh::lean_dec(v___x_6511_);
                    crate::leanh::lean_inc_ref(v_impl_6447_);
                    if v_isShared_6465_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6464_, 4, v_impl_6447_);
                        crate::leanh::lean_ctor_set(v___x_6464_, 3, v_r_6454_);
                        crate::leanh::lean_ctor_set(v___x_6464_, 2, v_v_6439_);
                        crate::leanh::lean_ctor_set(v___x_6464_, 1, v_k_6438_);
                        crate::leanh::lean_ctor_set(v___x_6464_, 0, v___x_6512_);
                        v___x_6514_ = v___x_6464_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6527_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v___x_6512_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 1, v_k_6438_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 2, v_v_6439_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 3, v_r_6454_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 4, v_impl_6447_);
                        v___x_6514_ = v_reuseFailAlloc_6527_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6478_ = lean_nat_add(v___x_6448_, v_size_6450_);
                crate::leanh::lean_dec(v_size_6450_);
                v___x_6479_ = lean_nat_add(v___x_6478_, v_size_6449_);
                crate::leanh::lean_dec(v___x_6478_);
                v___x_6491_ = lean_nat_add(v___x_6448_, v_size_6466_);
                if crate::leanh::lean_obj_tag(v_l_6470_) == 0 {
                    v_size_6501_ = crate::leanh::lean_ctor_get(v_l_6470_, 0);
                    crate::leanh::lean_inc(v_size_6501_);
                    v___y_6493_ = v_size_6501_;
                    state = 8;
                    continue;
                } else {
                    v___x_6502_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6493_ = v___x_6502_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_6484_ = lean_nat_add(v___y_6481_, v___y_6483_);
                crate::leanh::lean_dec(v___y_6483_);
                crate::leanh::lean_dec(v___y_6481_);
                if v_isShared_6477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6476_, 4, v_impl_6447_);
                    crate::leanh::lean_ctor_set(v___x_6476_, 3, v_r_6471_);
                    crate::leanh::lean_ctor_set(v___x_6476_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v___x_6476_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v___x_6476_, 0, v___x_6484_);
                    v___x_6486_ = v___x_6476_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6490_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6490_, 0, v___x_6484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6490_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6490_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6490_, 3, v_r_6471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6490_, 4, v_impl_6447_);
                    v___x_6486_ = v_reuseFailAlloc_6490_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6464_, 4, v___x_6486_);
                    crate::leanh::lean_ctor_set(v___x_6464_, 3, v___y_6482_);
                    crate::leanh::lean_ctor_set(v___x_6464_, 2, v_v_6469_);
                    crate::leanh::lean_ctor_set(v___x_6464_, 1, v_k_6468_);
                    crate::leanh::lean_ctor_set(v___x_6464_, 0, v___x_6479_);
                    v___x_6488_ = v___x_6464_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6489_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 0, v___x_6479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 1, v_k_6468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 2, v_v_6469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 3, v___y_6482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6489_, 4, v___x_6486_);
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
                crate::leanh::lean_dec(v___y_6493_);
                crate::leanh::lean_dec(v___x_6491_);
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v_l_6470_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v_l_6453_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 2, v_v_6452_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 1, v_k_6451_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6494_);
                    v___x_6496_ = v___x_6443_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6500_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 0, v___x_6494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 1, v_k_6451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 2, v_v_6452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 3, v_l_6453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 4, v_l_6470_);
                    v___x_6496_ = v_reuseFailAlloc_6500_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6497_ = lean_nat_add(v___x_6448_, v_size_6449_);
                crate::leanh::lean_dec(v_size_6449_);
                if crate::leanh::lean_obj_tag(v_r_6471_) == 0 {
                    v_size_6498_ = crate::leanh::lean_ctor_get(v_r_6471_, 0);
                    crate::leanh::lean_inc(v_size_6498_);
                    v___y_6481_ = v___x_6497_;
                    v___y_6482_ = v___x_6496_;
                    v___y_6483_ = v_size_6498_;
                    state = 5;
                    continue;
                } else {
                    v___x_6499_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6481_ = v___x_6497_;
                    v___y_6482_ = v___x_6496_;
                    v___y_6483_ = v___x_6499_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_6521_ = (!crate::leanh::lean_is_exclusive(v_impl_6447_)) as u8;
                if v_isSharedCheck_6521_ == 0 {
                    v_unused_6522_ = crate::leanh::lean_ctor_get(v_impl_6447_, 4);
                    crate::leanh::lean_dec(v_unused_6522_);
                    v_unused_6523_ = crate::leanh::lean_ctor_get(v_impl_6447_, 3);
                    crate::leanh::lean_dec(v_unused_6523_);
                    v_unused_6524_ = crate::leanh::lean_ctor_get(v_impl_6447_, 2);
                    crate::leanh::lean_dec(v_unused_6524_);
                    v_unused_6525_ = crate::leanh::lean_ctor_get(v_impl_6447_, 1);
                    crate::leanh::lean_dec(v_unused_6525_);
                    v_unused_6526_ = crate::leanh::lean_ctor_get(v_impl_6447_, 0);
                    crate::leanh::lean_dec(v_unused_6526_);
                    v___x_6516_ = v_impl_6447_;
                    v_isShared_6517_ = v_isSharedCheck_6521_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_6447_);
                    v___x_6516_ = crate::leanh::lean_box(0);
                    v_isShared_6517_ = v_isSharedCheck_6521_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_6517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6516_, 4, v___x_6514_);
                    crate::leanh::lean_ctor_set(v___x_6516_, 3, v_l_6453_);
                    crate::leanh::lean_ctor_set(v___x_6516_, 2, v_v_6452_);
                    crate::leanh::lean_ctor_set(v___x_6516_, 1, v_k_6451_);
                    crate::leanh::lean_ctor_set(v___x_6516_, 0, v___x_6510_);
                    v___x_6519_ = v___x_6516_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6520_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6520_, 0, v___x_6510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6520_, 1, v_k_6451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6520_, 2, v_v_6452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6520_, 3, v_l_6453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6520_, 4, v___x_6514_);
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
                v_size_6547_ = crate::leanh::lean_ctor_get(v_r_6540_, 0);
                v___x_6548_ = lean_nat_add(v___x_6448_, v_size_6541_);
                crate::leanh::lean_dec(v_size_6541_);
                v___x_6549_ = lean_nat_add(v___x_6448_, v_size_6547_);
                if v_isShared_6546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6545_, 4, v_impl_6447_);
                    crate::leanh::lean_ctor_set(v___x_6545_, 3, v_r_6540_);
                    crate::leanh::lean_ctor_set(v___x_6545_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v___x_6545_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v___x_6545_, 0, v___x_6549_);
                    v___x_6551_ = v___x_6545_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6555_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6555_, 0, v___x_6549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6555_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6555_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6555_, 3, v_r_6540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6555_, 4, v_impl_6447_);
                    v___x_6551_ = v_reuseFailAlloc_6555_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v___x_6551_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v_l_6539_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 2, v_v_6543_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 1, v_k_6542_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6548_);
                    v___x_6553_ = v___x_6443_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6554_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 0, v___x_6548_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 1, v_k_6542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 2, v_v_6543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 3, v_l_6539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6554_, 4, v___x_6551_);
                    v___x_6553_ = v_reuseFailAlloc_6554_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6553_;
            }
            17 => {
                v___x_6564_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_6563_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6562_, 3, v_r_6540_);
                    crate::leanh::lean_ctor_set(v___x_6562_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v___x_6562_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v___x_6562_, 0, v___x_6448_);
                    v___x_6566_ = v___x_6562_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6570_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6570_, 0, v___x_6448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6570_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6570_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6570_, 3, v_r_6540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6570_, 4, v_r_6540_);
                    v___x_6566_ = v_reuseFailAlloc_6570_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v___x_6566_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v_l_6539_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 2, v_v_6560_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 1, v_k_6559_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6564_);
                    v___x_6568_ = v___x_6443_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6569_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6569_, 0, v___x_6564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6569_, 1, v_k_6559_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6569_, 2, v_v_6560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6569_, 3, v_l_6539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6569_, 4, v___x_6566_);
                    v___x_6568_ = v_reuseFailAlloc_6569_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6568_;
            }
            20 => {
                v_k_6581_ = crate::leanh::lean_ctor_get(v_r_6575_, 1);
                v_v_6582_ = crate::leanh::lean_ctor_get(v_r_6575_, 2);
                v_isSharedCheck_6596_ = (!crate::leanh::lean_is_exclusive(v_r_6575_)) as u8;
                if v_isSharedCheck_6596_ == 0 {
                    v_unused_6597_ = crate::leanh::lean_ctor_get(v_r_6575_, 4);
                    crate::leanh::lean_dec(v_unused_6597_);
                    v_unused_6598_ = crate::leanh::lean_ctor_get(v_r_6575_, 3);
                    crate::leanh::lean_dec(v_unused_6598_);
                    v_unused_6599_ = crate::leanh::lean_ctor_get(v_r_6575_, 0);
                    crate::leanh::lean_dec(v_unused_6599_);
                    v___x_6584_ = v_r_6575_;
                    v_isShared_6585_ = v_isSharedCheck_6596_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_6582_);
                    crate::leanh::lean_inc(v_k_6581_);
                    crate::leanh::lean_dec(v_r_6575_);
                    v___x_6584_ = crate::leanh::lean_box(0);
                    v_isShared_6585_ = v_isSharedCheck_6596_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_6586_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_6585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6584_, 4, v_l_6539_);
                    crate::leanh::lean_ctor_set(v___x_6584_, 3, v_l_6539_);
                    crate::leanh::lean_ctor_set(v___x_6584_, 2, v_v_6577_);
                    crate::leanh::lean_ctor_set(v___x_6584_, 1, v_k_6576_);
                    crate::leanh::lean_ctor_set(v___x_6584_, 0, v___x_6448_);
                    v___x_6588_ = v___x_6584_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6595_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6595_, 0, v___x_6448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6595_, 1, v_k_6576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6595_, 2, v_v_6577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6595_, 3, v_l_6539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6595_, 4, v_l_6539_);
                    v___x_6588_ = v_reuseFailAlloc_6595_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_6580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6579_, 4, v_l_6539_);
                    crate::leanh::lean_ctor_set(v___x_6579_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v___x_6579_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v___x_6579_, 0, v___x_6448_);
                    v___x_6590_ = v___x_6579_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 0, v___x_6448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 3, v_l_6539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6594_, 4, v_l_6539_);
                    v___x_6590_ = v_reuseFailAlloc_6594_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v___x_6590_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v___x_6588_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 2, v_v_6582_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 1, v_k_6581_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6586_);
                    v___x_6592_ = v___x_6443_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6593_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 0, v___x_6586_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 1, v_k_6581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 2, v_v_6582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 3, v___x_6588_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6593_, 4, v___x_6590_);
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
                v_tree_6627_ = crate::leanh::lean_ctor_get(v___x_6626_, 2);
                crate::leanh::lean_inc(v_tree_6627_);
                if crate::leanh::lean_obj_tag(v_tree_6627_) == 0 {
                    v_k_6628_ = crate::leanh::lean_ctor_get(v___x_6626_, 0);
                    crate::leanh::lean_inc(v_k_6628_);
                    v_v_6629_ = crate::leanh::lean_ctor_get(v___x_6626_, 1);
                    crate::leanh::lean_inc(v_v_6629_);
                    crate::leanh::lean_dec_ref(v___x_6626_);
                    v_size_6630_ = crate::leanh::lean_ctor_get(v_tree_6627_, 0);
                    v___x_6631_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6632_ = lean_nat_mul(v___x_6631_, v_size_6630_);
                    v___x_6633_ = lean_nat_dec_lt(v___x_6632_, v_size_6616_);
                    crate::leanh::lean_dec(v___x_6632_);
                    if v___x_6633_ == 0 {
                        crate::leanh::lean_dec(v_l_6619_);
                        v___x_6634_ = lean_nat_add(v___x_6621_, v_size_6630_);
                        v___x_6635_ = lean_nat_add(v___x_6634_, v_size_6616_);
                        crate::leanh::lean_dec(v___x_6634_);
                        if v_isShared_6625_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6624_, 4, v_r_6441_);
                            crate::leanh::lean_ctor_set(v___x_6624_, 3, v_tree_6627_);
                            crate::leanh::lean_ctor_set(v___x_6624_, 2, v_v_6629_);
                            crate::leanh::lean_ctor_set(v___x_6624_, 1, v_k_6628_);
                            crate::leanh::lean_ctor_set(v___x_6624_, 0, v___x_6635_);
                            v___x_6637_ = v___x_6624_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_6638_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 0, v___x_6635_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 1, v_k_6628_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 2, v_v_6629_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 3, v_tree_6627_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 4, v_r_6441_);
                            v___x_6637_ = v_reuseFailAlloc_6638_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_6620_);
                        crate::leanh::lean_inc(v_v_6618_);
                        crate::leanh::lean_inc(v_k_6617_);
                        crate::leanh::lean_inc(v_size_6616_);
                        v_isSharedCheck_6693_ = (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                        if v_isSharedCheck_6693_ == 0 {
                            v_unused_6694_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                            crate::leanh::lean_dec(v_unused_6694_);
                            v_unused_6695_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                            crate::leanh::lean_dec(v_unused_6695_);
                            v_unused_6696_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                            crate::leanh::lean_dec(v_unused_6696_);
                            v_unused_6697_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                            crate::leanh::lean_dec(v_unused_6697_);
                            v_unused_6698_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                            crate::leanh::lean_dec(v_unused_6698_);
                            v___x_6640_ = v_r_6441_;
                            v_isShared_6641_ = v_isSharedCheck_6693_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_6441_);
                            v___x_6640_ = crate::leanh::lean_box(0);
                            v_isShared_6641_ = v_isSharedCheck_6693_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_6620_);
                    crate::leanh::lean_inc(v_v_6618_);
                    crate::leanh::lean_inc(v_k_6617_);
                    crate::leanh::lean_inc(v_size_6616_);
                    v_isSharedCheck_6752_ = (!crate::leanh::lean_is_exclusive(v_r_6441_)) as u8;
                    if v_isSharedCheck_6752_ == 0 {
                        v_unused_6753_ = crate::leanh::lean_ctor_get(v_r_6441_, 4);
                        crate::leanh::lean_dec(v_unused_6753_);
                        v_unused_6754_ = crate::leanh::lean_ctor_get(v_r_6441_, 3);
                        crate::leanh::lean_dec(v_unused_6754_);
                        v_unused_6755_ = crate::leanh::lean_ctor_get(v_r_6441_, 2);
                        crate::leanh::lean_dec(v_unused_6755_);
                        v_unused_6756_ = crate::leanh::lean_ctor_get(v_r_6441_, 1);
                        crate::leanh::lean_dec(v_unused_6756_);
                        v_unused_6757_ = crate::leanh::lean_ctor_get(v_r_6441_, 0);
                        crate::leanh::lean_dec(v_unused_6757_);
                        v___x_6700_ = v_r_6441_;
                        v_isShared_6701_ = v_isSharedCheck_6752_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_6441_);
                        v___x_6700_ = crate::leanh::lean_box(0);
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
                v_size_6642_ = crate::leanh::lean_ctor_get(v_l_6619_, 0);
                v_k_6643_ = crate::leanh::lean_ctor_get(v_l_6619_, 1);
                v_v_6644_ = crate::leanh::lean_ctor_get(v_l_6619_, 2);
                v_l_6645_ = crate::leanh::lean_ctor_get(v_l_6619_, 3);
                v_r_6646_ = crate::leanh::lean_ctor_get(v_l_6619_, 4);
                v_size_6647_ = crate::leanh::lean_ctor_get(v_r_6620_, 0);
                v___x_6648_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6649_ = lean_nat_mul(v___x_6648_, v_size_6647_);
                v___x_6650_ = lean_nat_dec_lt(v_size_6642_, v___x_6649_);
                crate::leanh::lean_dec(v___x_6649_);
                if v___x_6650_ == 0 {
                    crate::leanh::lean_inc(v_r_6646_);
                    crate::leanh::lean_inc(v_l_6645_);
                    crate::leanh::lean_inc(v_v_6644_);
                    crate::leanh::lean_inc(v_k_6643_);
                    v_isSharedCheck_6678_ = (!crate::leanh::lean_is_exclusive(v_l_6619_)) as u8;
                    if v_isSharedCheck_6678_ == 0 {
                        v_unused_6679_ = crate::leanh::lean_ctor_get(v_l_6619_, 4);
                        crate::leanh::lean_dec(v_unused_6679_);
                        v_unused_6680_ = crate::leanh::lean_ctor_get(v_l_6619_, 3);
                        crate::leanh::lean_dec(v_unused_6680_);
                        v_unused_6681_ = crate::leanh::lean_ctor_get(v_l_6619_, 2);
                        crate::leanh::lean_dec(v_unused_6681_);
                        v_unused_6682_ = crate::leanh::lean_ctor_get(v_l_6619_, 1);
                        crate::leanh::lean_dec(v_unused_6682_);
                        v_unused_6683_ = crate::leanh::lean_ctor_get(v_l_6619_, 0);
                        crate::leanh::lean_dec(v_unused_6683_);
                        v___x_6652_ = v_l_6619_;
                        v_isShared_6653_ = v_isSharedCheck_6678_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_6619_);
                        v___x_6652_ = crate::leanh::lean_box(0);
                        v_isShared_6653_ = v_isSharedCheck_6678_;
                        state = 30;
                        continue;
                    }
                } else {
                    v___x_6684_ = lean_nat_add(v___x_6621_, v_size_6630_);
                    v___x_6685_ = lean_nat_add(v___x_6684_, v_size_6616_);
                    crate::leanh::lean_dec(v_size_6616_);
                    v___x_6686_ = lean_nat_add(v___x_6684_, v_size_6642_);
                    crate::leanh::lean_dec(v___x_6684_);
                    if v_isShared_6641_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6640_, 4, v_l_6619_);
                        crate::leanh::lean_ctor_set(v___x_6640_, 3, v_tree_6627_);
                        crate::leanh::lean_ctor_set(v___x_6640_, 2, v_v_6629_);
                        crate::leanh::lean_ctor_set(v___x_6640_, 1, v_k_6628_);
                        crate::leanh::lean_ctor_set(v___x_6640_, 0, v___x_6686_);
                        v___x_6688_ = v___x_6640_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_6692_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6692_, 0, v___x_6686_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6692_, 1, v_k_6628_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6692_, 2, v_v_6629_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6692_, 3, v_tree_6627_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6692_, 4, v_l_6619_);
                        v___x_6688_ = v_reuseFailAlloc_6692_;
                        state = 36;
                        continue;
                    }
                }
            }
            30 => {
                v___x_6654_ = lean_nat_add(v___x_6621_, v_size_6630_);
                v___x_6655_ = lean_nat_add(v___x_6654_, v_size_6616_);
                crate::leanh::lean_dec(v_size_6616_);
                if crate::leanh::lean_obj_tag(v_l_6645_) == 0 {
                    v_size_6676_ = crate::leanh::lean_ctor_get(v_l_6645_, 0);
                    crate::leanh::lean_inc(v_size_6676_);
                    v___y_6668_ = v_size_6676_;
                    state = 34;
                    continue;
                } else {
                    v___x_6677_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6668_ = v___x_6677_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_6660_ = lean_nat_add(v___y_6658_, v___y_6659_);
                crate::leanh::lean_dec(v___y_6659_);
                crate::leanh::lean_dec(v___y_6658_);
                if v_isShared_6653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6652_, 4, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6652_, 3, v_r_6646_);
                    crate::leanh::lean_ctor_set(v___x_6652_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v___x_6652_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v___x_6652_, 0, v___x_6660_);
                    v___x_6662_ = v___x_6652_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6666_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6666_, 0, v___x_6660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6666_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6666_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6666_, 3, v_r_6646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6666_, 4, v_r_6620_);
                    v___x_6662_ = v_reuseFailAlloc_6666_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_6641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6640_, 4, v___x_6662_);
                    crate::leanh::lean_ctor_set(v___x_6640_, 3, v___y_6657_);
                    crate::leanh::lean_ctor_set(v___x_6640_, 2, v_v_6644_);
                    crate::leanh::lean_ctor_set(v___x_6640_, 1, v_k_6643_);
                    crate::leanh::lean_ctor_set(v___x_6640_, 0, v___x_6655_);
                    v___x_6664_ = v___x_6640_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6665_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6665_, 0, v___x_6655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6665_, 1, v_k_6643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6665_, 2, v_v_6644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6665_, 3, v___y_6657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6665_, 4, v___x_6662_);
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
                crate::leanh::lean_dec(v___y_6668_);
                crate::leanh::lean_dec(v___x_6654_);
                if v_isShared_6625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6624_, 4, v_l_6645_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 3, v_tree_6627_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 2, v_v_6629_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 1, v_k_6628_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 0, v___x_6669_);
                    v___x_6671_ = v___x_6624_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6675_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6675_, 0, v___x_6669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6675_, 1, v_k_6628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6675_, 2, v_v_6629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6675_, 3, v_tree_6627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6675_, 4, v_l_6645_);
                    v___x_6671_ = v_reuseFailAlloc_6675_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_6672_ = lean_nat_add(v___x_6621_, v_size_6647_);
                if crate::leanh::lean_obj_tag(v_r_6646_) == 0 {
                    v_size_6673_ = crate::leanh::lean_ctor_get(v_r_6646_, 0);
                    crate::leanh::lean_inc(v_size_6673_);
                    v___y_6657_ = v___x_6671_;
                    v___y_6658_ = v___x_6672_;
                    v___y_6659_ = v_size_6673_;
                    state = 31;
                    continue;
                } else {
                    v___x_6674_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6657_ = v___x_6671_;
                    v___y_6658_ = v___x_6672_;
                    v___y_6659_ = v___x_6674_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_6625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6624_, 4, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 3, v___x_6688_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 0, v___x_6685_);
                    v___x_6690_ = v___x_6624_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6691_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6691_, 0, v___x_6685_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6691_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6691_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6691_, 3, v___x_6688_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6691_, 4, v_r_6620_);
                    v___x_6690_ = v_reuseFailAlloc_6691_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6690_;
            }
            38 => {
                if crate::leanh::lean_obj_tag(v_l_6619_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_6620_) == 0 {
                        v_k_6702_ = crate::leanh::lean_ctor_get(v___x_6626_, 0);
                        crate::leanh::lean_inc(v_k_6702_);
                        v_v_6703_ = crate::leanh::lean_ctor_get(v___x_6626_, 1);
                        crate::leanh::lean_inc(v_v_6703_);
                        crate::leanh::lean_dec_ref(v___x_6626_);
                        v_size_6704_ = crate::leanh::lean_ctor_get(v_l_6619_, 0);
                        v___x_6705_ = lean_nat_add(v___x_6621_, v_size_6616_);
                        crate::leanh::lean_dec(v_size_6616_);
                        v___x_6706_ = lean_nat_add(v___x_6621_, v_size_6704_);
                        if v_isShared_6701_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6700_, 4, v_l_6619_);
                            crate::leanh::lean_ctor_set(v___x_6700_, 3, v_tree_6627_);
                            crate::leanh::lean_ctor_set(v___x_6700_, 2, v_v_6703_);
                            crate::leanh::lean_ctor_set(v___x_6700_, 1, v_k_6702_);
                            crate::leanh::lean_ctor_set(v___x_6700_, 0, v___x_6706_);
                            v___x_6708_ = v___x_6700_;
                            state = 39;
                            continue;
                        } else {
                            v_reuseFailAlloc_6712_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 0, v___x_6706_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 1, v_k_6702_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 2, v_v_6703_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 3, v_tree_6627_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 4, v_l_6619_);
                            v___x_6708_ = v_reuseFailAlloc_6712_;
                            state = 39;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_6616_);
                        v_k_6713_ = crate::leanh::lean_ctor_get(v___x_6626_, 0);
                        crate::leanh::lean_inc(v_k_6713_);
                        v_v_6714_ = crate::leanh::lean_ctor_get(v___x_6626_, 1);
                        crate::leanh::lean_inc(v_v_6714_);
                        crate::leanh::lean_dec_ref(v___x_6626_);
                        v_k_6715_ = crate::leanh::lean_ctor_get(v_l_6619_, 1);
                        v_v_6716_ = crate::leanh::lean_ctor_get(v_l_6619_, 2);
                        v_isSharedCheck_6730_ = (!crate::leanh::lean_is_exclusive(v_l_6619_)) as u8;
                        if v_isSharedCheck_6730_ == 0 {
                            v_unused_6731_ = crate::leanh::lean_ctor_get(v_l_6619_, 4);
                            crate::leanh::lean_dec(v_unused_6731_);
                            v_unused_6732_ = crate::leanh::lean_ctor_get(v_l_6619_, 3);
                            crate::leanh::lean_dec(v_unused_6732_);
                            v_unused_6733_ = crate::leanh::lean_ctor_get(v_l_6619_, 0);
                            crate::leanh::lean_dec(v_unused_6733_);
                            v___x_6718_ = v_l_6619_;
                            v_isShared_6719_ = v_isSharedCheck_6730_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_6716_);
                            crate::leanh::lean_inc(v_k_6715_);
                            crate::leanh::lean_dec(v_l_6619_);
                            v___x_6718_ = crate::leanh::lean_box(0);
                            v_isShared_6719_ = v_isSharedCheck_6730_;
                            state = 41;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_6620_) == 0 {
                        crate::leanh::lean_dec(v_size_6616_);
                        v_k_6734_ = crate::leanh::lean_ctor_get(v___x_6626_, 0);
                        crate::leanh::lean_inc(v_k_6734_);
                        v_v_6735_ = crate::leanh::lean_ctor_get(v___x_6626_, 1);
                        crate::leanh::lean_inc(v_v_6735_);
                        crate::leanh::lean_dec_ref(v___x_6626_);
                        v___x_6736_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_6701_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6700_, 4, v_l_6619_);
                            crate::leanh::lean_ctor_set(v___x_6700_, 2, v_v_6735_);
                            crate::leanh::lean_ctor_set(v___x_6700_, 1, v_k_6734_);
                            crate::leanh::lean_ctor_set(v___x_6700_, 0, v___x_6621_);
                            v___x_6738_ = v___x_6700_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_6742_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 0, v___x_6621_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 1, v_k_6734_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 2, v_v_6735_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 3, v_l_6619_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 4, v_l_6619_);
                            v___x_6738_ = v_reuseFailAlloc_6742_;
                            state = 45;
                            continue;
                        }
                    } else {
                        v_k_6743_ = crate::leanh::lean_ctor_get(v___x_6626_, 0);
                        crate::leanh::lean_inc(v_k_6743_);
                        v_v_6744_ = crate::leanh::lean_ctor_get(v___x_6626_, 1);
                        crate::leanh::lean_inc(v_v_6744_);
                        crate::leanh::lean_dec_ref(v___x_6626_);
                        if v_isShared_6701_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6700_, 3, v_r_6620_);
                            v___x_6746_ = v___x_6700_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_6751_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_size_6616_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 1, v_k_6617_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 2, v_v_6618_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 3, v_r_6620_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6751_, 4, v_r_6620_);
                            v___x_6746_ = v_reuseFailAlloc_6751_;
                            state = 47;
                            continue;
                        }
                    }
                }
            }
            39 => {
                if v_isShared_6625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6624_, 4, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 3, v___x_6708_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 0, v___x_6705_);
                    v___x_6710_ = v___x_6624_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6711_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6711_, 0, v___x_6705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6711_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6711_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6711_, 3, v___x_6708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6711_, 4, v_r_6620_);
                    v___x_6710_ = v_reuseFailAlloc_6711_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_6710_;
            }
            41 => {
                v___x_6720_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_6719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6718_, 4, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6718_, 3, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6718_, 2, v_v_6714_);
                    crate::leanh::lean_ctor_set(v___x_6718_, 1, v_k_6713_);
                    crate::leanh::lean_ctor_set(v___x_6718_, 0, v___x_6621_);
                    v___x_6722_ = v___x_6718_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_6729_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 0, v___x_6621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 1, v_k_6713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 2, v_v_6714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 3, v_r_6620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 4, v_r_6620_);
                    v___x_6722_ = v_reuseFailAlloc_6729_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_6701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6700_, 3, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6700_, 0, v___x_6621_);
                    v___x_6724_ = v___x_6700_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_6728_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6728_, 0, v___x_6621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6728_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6728_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6728_, 3, v_r_6620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6728_, 4, v_r_6620_);
                    v___x_6724_ = v_reuseFailAlloc_6728_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_6625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6624_, 4, v___x_6724_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 3, v___x_6722_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 2, v_v_6716_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 1, v_k_6715_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 0, v___x_6720_);
                    v___x_6726_ = v___x_6624_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6727_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6727_, 0, v___x_6720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6727_, 1, v_k_6715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6727_, 2, v_v_6716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6727_, 3, v___x_6722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6727_, 4, v___x_6724_);
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
                    crate::leanh::lean_ctor_set(v___x_6624_, 4, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 3, v___x_6738_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 0, v___x_6736_);
                    v___x_6740_ = v___x_6624_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6741_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6741_, 0, v___x_6736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6741_, 1, v_k_6617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6741_, 2, v_v_6618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6741_, 3, v___x_6738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6741_, 4, v_r_6620_);
                    v___x_6740_ = v_reuseFailAlloc_6741_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_6740_;
            }
            47 => {
                v___x_6747_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_6625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6624_, 4, v___x_6746_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 3, v_r_6620_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 2, v_v_6744_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 1, v_k_6743_);
                    crate::leanh::lean_ctor_set(v___x_6624_, 0, v___x_6747_);
                    v___x_6749_ = v___x_6624_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_6750_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 0, v___x_6747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 1, v_k_6743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 2, v_v_6744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 3, v_r_6620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 4, v___x_6746_);
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
                v_tree_6768_ = crate::leanh::lean_ctor_get(v___x_6767_, 2);
                crate::leanh::lean_inc(v_tree_6768_);
                if crate::leanh::lean_obj_tag(v_tree_6768_) == 0 {
                    v_k_6769_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                    crate::leanh::lean_inc(v_k_6769_);
                    v_v_6770_ = crate::leanh::lean_ctor_get(v___x_6767_, 1);
                    crate::leanh::lean_inc(v_v_6770_);
                    crate::leanh::lean_dec_ref(v___x_6767_);
                    v_size_6771_ = crate::leanh::lean_ctor_get(v_tree_6768_, 0);
                    v___x_6772_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6773_ = lean_nat_mul(v___x_6772_, v_size_6771_);
                    v___x_6774_ = lean_nat_dec_lt(v___x_6773_, v_size_6611_);
                    crate::leanh::lean_dec(v___x_6773_);
                    if v___x_6774_ == 0 {
                        crate::leanh::lean_dec(v_r_6615_);
                        v___x_6775_ = lean_nat_add(v___x_6621_, v_size_6611_);
                        v___x_6776_ = lean_nat_add(v___x_6775_, v_size_6771_);
                        crate::leanh::lean_dec(v___x_6775_);
                        if v_isShared_6766_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6765_, 4, v_tree_6768_);
                            crate::leanh::lean_ctor_set(v___x_6765_, 3, v_l_6440_);
                            crate::leanh::lean_ctor_set(v___x_6765_, 2, v_v_6770_);
                            crate::leanh::lean_ctor_set(v___x_6765_, 1, v_k_6769_);
                            crate::leanh::lean_ctor_set(v___x_6765_, 0, v___x_6776_);
                            v___x_6778_ = v___x_6765_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_6779_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6779_, 0, v___x_6776_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6779_, 1, v_k_6769_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6779_, 2, v_v_6770_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6779_, 3, v_l_6440_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6779_, 4, v_tree_6768_);
                            v___x_6778_ = v_reuseFailAlloc_6779_;
                            state = 50;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_6614_);
                        crate::leanh::lean_inc(v_v_6613_);
                        crate::leanh::lean_inc(v_k_6612_);
                        crate::leanh::lean_inc(v_size_6611_);
                        v_isSharedCheck_6845_ = (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                        if v_isSharedCheck_6845_ == 0 {
                            v_unused_6846_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                            crate::leanh::lean_dec(v_unused_6846_);
                            v_unused_6847_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                            crate::leanh::lean_dec(v_unused_6847_);
                            v_unused_6848_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                            crate::leanh::lean_dec(v_unused_6848_);
                            v_unused_6849_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                            crate::leanh::lean_dec(v_unused_6849_);
                            v_unused_6850_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                            crate::leanh::lean_dec(v_unused_6850_);
                            v___x_6781_ = v_l_6440_;
                            v_isShared_6782_ = v_isSharedCheck_6845_;
                            state = 51;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_6440_);
                            v___x_6781_ = crate::leanh::lean_box(0);
                            v_isShared_6782_ = v_isSharedCheck_6845_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_6614_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_6614_);
                        crate::leanh::lean_inc(v_v_6613_);
                        crate::leanh::lean_inc(v_k_6612_);
                        crate::leanh::lean_inc(v_size_6611_);
                        v_isSharedCheck_6874_ = (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                        if v_isSharedCheck_6874_ == 0 {
                            v_unused_6875_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                            crate::leanh::lean_dec(v_unused_6875_);
                            v_unused_6876_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                            crate::leanh::lean_dec(v_unused_6876_);
                            v_unused_6877_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                            crate::leanh::lean_dec(v_unused_6877_);
                            v_unused_6878_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                            crate::leanh::lean_dec(v_unused_6878_);
                            v_unused_6879_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                            crate::leanh::lean_dec(v_unused_6879_);
                            v___x_6852_ = v_l_6440_;
                            v_isShared_6853_ = v_isSharedCheck_6874_;
                            state = 61;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_6440_);
                            v___x_6852_ = crate::leanh::lean_box(0);
                            v_isShared_6853_ = v_isSharedCheck_6874_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_6615_) == 0 {
                            crate::leanh::lean_inc(v_l_6614_);
                            crate::leanh::lean_inc(v_v_6613_);
                            crate::leanh::lean_inc(v_k_6612_);
                            v_isSharedCheck_6904_ =
                                (!crate::leanh::lean_is_exclusive(v_l_6440_)) as u8;
                            if v_isSharedCheck_6904_ == 0 {
                                v_unused_6905_ = crate::leanh::lean_ctor_get(v_l_6440_, 4);
                                crate::leanh::lean_dec(v_unused_6905_);
                                v_unused_6906_ = crate::leanh::lean_ctor_get(v_l_6440_, 3);
                                crate::leanh::lean_dec(v_unused_6906_);
                                v_unused_6907_ = crate::leanh::lean_ctor_get(v_l_6440_, 2);
                                crate::leanh::lean_dec(v_unused_6907_);
                                v_unused_6908_ = crate::leanh::lean_ctor_get(v_l_6440_, 1);
                                crate::leanh::lean_dec(v_unused_6908_);
                                v_unused_6909_ = crate::leanh::lean_ctor_get(v_l_6440_, 0);
                                crate::leanh::lean_dec(v_unused_6909_);
                                v___x_6881_ = v_l_6440_;
                                v_isShared_6882_ = v_isSharedCheck_6904_;
                                state = 66;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_6440_);
                                v___x_6881_ = crate::leanh::lean_box(0);
                                v_isShared_6882_ = v_isSharedCheck_6904_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_6910_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                            crate::leanh::lean_inc(v_k_6910_);
                            v_v_6911_ = crate::leanh::lean_ctor_get(v___x_6767_, 1);
                            crate::leanh::lean_inc(v_v_6911_);
                            crate::leanh::lean_dec_ref(v___x_6767_);
                            v___x_6912_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_6766_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6765_, 4, v_r_6615_);
                                crate::leanh::lean_ctor_set(v___x_6765_, 3, v_l_6440_);
                                crate::leanh::lean_ctor_set(v___x_6765_, 2, v_v_6911_);
                                crate::leanh::lean_ctor_set(v___x_6765_, 1, v_k_6910_);
                                crate::leanh::lean_ctor_set(v___x_6765_, 0, v___x_6912_);
                                v___x_6914_ = v___x_6765_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_6915_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6912_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 1, v_k_6910_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 2, v_v_6911_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 3, v_l_6440_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 4, v_r_6615_);
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
                v_size_6783_ = crate::leanh::lean_ctor_get(v_l_6614_, 0);
                v_size_6784_ = crate::leanh::lean_ctor_get(v_r_6615_, 0);
                v_k_6785_ = crate::leanh::lean_ctor_get(v_r_6615_, 1);
                v_v_6786_ = crate::leanh::lean_ctor_get(v_r_6615_, 2);
                v_l_6787_ = crate::leanh::lean_ctor_get(v_r_6615_, 3);
                v_r_6788_ = crate::leanh::lean_ctor_get(v_r_6615_, 4);
                v___x_6789_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6790_ = lean_nat_mul(v___x_6789_, v_size_6783_);
                v___x_6791_ = lean_nat_dec_lt(v_size_6784_, v___x_6790_);
                crate::leanh::lean_dec(v___x_6790_);
                if v___x_6791_ == 0 {
                    crate::leanh::lean_inc(v_r_6788_);
                    crate::leanh::lean_inc(v_l_6787_);
                    crate::leanh::lean_inc(v_v_6786_);
                    crate::leanh::lean_inc(v_k_6785_);
                    crate::leanh::lean_del_object(v___x_6781_);
                    v_isSharedCheck_6829_ = (!crate::leanh::lean_is_exclusive(v_r_6615_)) as u8;
                    if v_isSharedCheck_6829_ == 0 {
                        v_unused_6830_ = crate::leanh::lean_ctor_get(v_r_6615_, 4);
                        crate::leanh::lean_dec(v_unused_6830_);
                        v_unused_6831_ = crate::leanh::lean_ctor_get(v_r_6615_, 3);
                        crate::leanh::lean_dec(v_unused_6831_);
                        v_unused_6832_ = crate::leanh::lean_ctor_get(v_r_6615_, 2);
                        crate::leanh::lean_dec(v_unused_6832_);
                        v_unused_6833_ = crate::leanh::lean_ctor_get(v_r_6615_, 1);
                        crate::leanh::lean_dec(v_unused_6833_);
                        v_unused_6834_ = crate::leanh::lean_ctor_get(v_r_6615_, 0);
                        crate::leanh::lean_dec(v_unused_6834_);
                        v___x_6793_ = v_r_6615_;
                        v_isShared_6794_ = v_isSharedCheck_6829_;
                        state = 52;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_6615_);
                        v___x_6793_ = crate::leanh::lean_box(0);
                        v_isShared_6794_ = v_isSharedCheck_6829_;
                        state = 52;
                        continue;
                    }
                } else {
                    v___x_6835_ = lean_nat_add(v___x_6621_, v_size_6611_);
                    crate::leanh::lean_dec(v_size_6611_);
                    v___x_6836_ = lean_nat_add(v___x_6835_, v_size_6771_);
                    crate::leanh::lean_dec(v___x_6835_);
                    v___x_6837_ = lean_nat_add(v___x_6621_, v_size_6771_);
                    v___x_6838_ = lean_nat_add(v___x_6837_, v_size_6784_);
                    crate::leanh::lean_dec(v___x_6837_);
                    if v_isShared_6766_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6765_, 4, v_tree_6768_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 3, v_r_6615_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 2, v_v_6770_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 1, v_k_6769_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 0, v___x_6838_);
                        v___x_6840_ = v___x_6765_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_6844_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 0, v___x_6838_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 1, v_k_6769_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 2, v_v_6770_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 3, v_r_6615_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6844_, 4, v_tree_6768_);
                        v___x_6840_ = v_reuseFailAlloc_6844_;
                        state = 59;
                        continue;
                    }
                }
            }
            52 => {
                v___x_6795_ = lean_nat_add(v___x_6621_, v_size_6611_);
                crate::leanh::lean_dec(v_size_6611_);
                v___x_6796_ = lean_nat_add(v___x_6795_, v_size_6771_);
                crate::leanh::lean_dec(v___x_6795_);
                v___x_6817_ = lean_nat_add(v___x_6621_, v_size_6783_);
                if crate::leanh::lean_obj_tag(v_l_6787_) == 0 {
                    v_size_6827_ = crate::leanh::lean_ctor_get(v_l_6787_, 0);
                    crate::leanh::lean_inc(v_size_6827_);
                    v___y_6819_ = v_size_6827_;
                    state = 57;
                    continue;
                } else {
                    v___x_6828_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6819_ = v___x_6828_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_6801_ = lean_nat_add(v___y_6798_, v___y_6800_);
                crate::leanh::lean_dec(v___y_6800_);
                crate::leanh::lean_dec(v___y_6798_);
                crate::leanh::lean_inc_ref(v_tree_6768_);
                if v_isShared_6794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6793_, 4, v_tree_6768_);
                    crate::leanh::lean_ctor_set(v___x_6793_, 3, v_r_6788_);
                    crate::leanh::lean_ctor_set(v___x_6793_, 2, v_v_6770_);
                    crate::leanh::lean_ctor_set(v___x_6793_, 1, v_k_6769_);
                    crate::leanh::lean_ctor_set(v___x_6793_, 0, v___x_6801_);
                    v___x_6803_ = v___x_6793_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_6816_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6816_, 0, v___x_6801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6816_, 1, v_k_6769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6816_, 2, v_v_6770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6816_, 3, v_r_6788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6816_, 4, v_tree_6768_);
                    v___x_6803_ = v_reuseFailAlloc_6816_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_6810_ = (!crate::leanh::lean_is_exclusive(v_tree_6768_)) as u8;
                if v_isSharedCheck_6810_ == 0 {
                    v_unused_6811_ = crate::leanh::lean_ctor_get(v_tree_6768_, 4);
                    crate::leanh::lean_dec(v_unused_6811_);
                    v_unused_6812_ = crate::leanh::lean_ctor_get(v_tree_6768_, 3);
                    crate::leanh::lean_dec(v_unused_6812_);
                    v_unused_6813_ = crate::leanh::lean_ctor_get(v_tree_6768_, 2);
                    crate::leanh::lean_dec(v_unused_6813_);
                    v_unused_6814_ = crate::leanh::lean_ctor_get(v_tree_6768_, 1);
                    crate::leanh::lean_dec(v_unused_6814_);
                    v_unused_6815_ = crate::leanh::lean_ctor_get(v_tree_6768_, 0);
                    crate::leanh::lean_dec(v_unused_6815_);
                    v___x_6805_ = v_tree_6768_;
                    v_isShared_6806_ = v_isSharedCheck_6810_;
                    state = 55;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_6768_);
                    v___x_6805_ = crate::leanh::lean_box(0);
                    v_isShared_6806_ = v_isSharedCheck_6810_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_6806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6805_, 4, v___x_6803_);
                    crate::leanh::lean_ctor_set(v___x_6805_, 3, v___y_6799_);
                    crate::leanh::lean_ctor_set(v___x_6805_, 2, v_v_6786_);
                    crate::leanh::lean_ctor_set(v___x_6805_, 1, v_k_6785_);
                    crate::leanh::lean_ctor_set(v___x_6805_, 0, v___x_6796_);
                    v___x_6808_ = v___x_6805_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_6809_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6809_, 0, v___x_6796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6809_, 1, v_k_6785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6809_, 2, v_v_6786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6809_, 3, v___y_6799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6809_, 4, v___x_6803_);
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
                crate::leanh::lean_dec(v___y_6819_);
                crate::leanh::lean_dec(v___x_6817_);
                if v_isShared_6766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6765_, 4, v_l_6787_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 2, v_v_6613_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 1, v_k_6612_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 0, v___x_6820_);
                    v___x_6822_ = v___x_6765_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_6826_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6826_, 0, v___x_6820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6826_, 1, v_k_6612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6826_, 2, v_v_6613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6826_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6826_, 4, v_l_6787_);
                    v___x_6822_ = v_reuseFailAlloc_6826_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_6823_ = lean_nat_add(v___x_6621_, v_size_6771_);
                if crate::leanh::lean_obj_tag(v_r_6788_) == 0 {
                    v_size_6824_ = crate::leanh::lean_ctor_get(v_r_6788_, 0);
                    crate::leanh::lean_inc(v_size_6824_);
                    v___y_6798_ = v___x_6823_;
                    v___y_6799_ = v___x_6822_;
                    v___y_6800_ = v_size_6824_;
                    state = 53;
                    continue;
                } else {
                    v___x_6825_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6798_ = v___x_6823_;
                    v___y_6799_ = v___x_6822_;
                    v___y_6800_ = v___x_6825_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_6782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6781_, 4, v___x_6840_);
                    crate::leanh::lean_ctor_set(v___x_6781_, 0, v___x_6836_);
                    v___x_6842_ = v___x_6781_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_6843_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 0, v___x_6836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 1, v_k_6612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 2, v_v_6613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 4, v___x_6840_);
                    v___x_6842_ = v_reuseFailAlloc_6843_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_6842_;
            }
            61 => {
                if crate::leanh::lean_obj_tag(v_r_6615_) == 0 {
                    v_k_6854_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                    crate::leanh::lean_inc(v_k_6854_);
                    v_v_6855_ = crate::leanh::lean_ctor_get(v___x_6767_, 1);
                    crate::leanh::lean_inc(v_v_6855_);
                    crate::leanh::lean_dec_ref(v___x_6767_);
                    v_size_6856_ = crate::leanh::lean_ctor_get(v_r_6615_, 0);
                    v___x_6857_ = lean_nat_add(v___x_6621_, v_size_6611_);
                    crate::leanh::lean_dec(v_size_6611_);
                    v___x_6858_ = lean_nat_add(v___x_6621_, v_size_6856_);
                    if v_isShared_6766_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6765_, 4, v_tree_6768_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 3, v_r_6615_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 2, v_v_6855_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 1, v_k_6854_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 0, v___x_6858_);
                        v___x_6860_ = v___x_6765_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_6864_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6864_, 0, v___x_6858_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6864_, 1, v_k_6854_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6864_, 2, v_v_6855_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6864_, 3, v_r_6615_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6864_, 4, v_tree_6768_);
                        v___x_6860_ = v_reuseFailAlloc_6864_;
                        state = 62;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_6611_);
                    v_k_6865_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                    crate::leanh::lean_inc(v_k_6865_);
                    v_v_6866_ = crate::leanh::lean_ctor_get(v___x_6767_, 1);
                    crate::leanh::lean_inc(v_v_6866_);
                    crate::leanh::lean_dec_ref(v___x_6767_);
                    v___x_6867_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_6766_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6765_, 4, v_r_6615_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 3, v_r_6615_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 2, v_v_6866_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 1, v_k_6865_);
                        crate::leanh::lean_ctor_set(v___x_6765_, 0, v___x_6621_);
                        v___x_6869_ = v___x_6765_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_6873_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6873_, 0, v___x_6621_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6873_, 1, v_k_6865_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6873_, 2, v_v_6866_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6873_, 3, v_r_6615_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6873_, 4, v_r_6615_);
                        v___x_6869_ = v_reuseFailAlloc_6873_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_6853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6852_, 4, v___x_6860_);
                    crate::leanh::lean_ctor_set(v___x_6852_, 0, v___x_6857_);
                    v___x_6862_ = v___x_6852_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_6863_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6863_, 0, v___x_6857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6863_, 1, v_k_6612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6863_, 2, v_v_6613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6863_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6863_, 4, v___x_6860_);
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
                    crate::leanh::lean_ctor_set(v___x_6852_, 4, v___x_6869_);
                    crate::leanh::lean_ctor_set(v___x_6852_, 0, v___x_6867_);
                    v___x_6871_ = v___x_6852_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_6872_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6872_, 0, v___x_6867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6872_, 1, v_k_6612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6872_, 2, v_v_6613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6872_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6872_, 4, v___x_6869_);
                    v___x_6871_ = v_reuseFailAlloc_6872_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_6871_;
            }
            66 => {
                v_k_6883_ = crate::leanh::lean_ctor_get(v___x_6767_, 0);
                crate::leanh::lean_inc(v_k_6883_);
                v_v_6884_ = crate::leanh::lean_ctor_get(v___x_6767_, 1);
                crate::leanh::lean_inc(v_v_6884_);
                crate::leanh::lean_dec_ref(v___x_6767_);
                v_k_6885_ = crate::leanh::lean_ctor_get(v_r_6615_, 1);
                v_v_6886_ = crate::leanh::lean_ctor_get(v_r_6615_, 2);
                v_isSharedCheck_6900_ = (!crate::leanh::lean_is_exclusive(v_r_6615_)) as u8;
                if v_isSharedCheck_6900_ == 0 {
                    v_unused_6901_ = crate::leanh::lean_ctor_get(v_r_6615_, 4);
                    crate::leanh::lean_dec(v_unused_6901_);
                    v_unused_6902_ = crate::leanh::lean_ctor_get(v_r_6615_, 3);
                    crate::leanh::lean_dec(v_unused_6902_);
                    v_unused_6903_ = crate::leanh::lean_ctor_get(v_r_6615_, 0);
                    crate::leanh::lean_dec(v_unused_6903_);
                    v___x_6888_ = v_r_6615_;
                    v_isShared_6889_ = v_isSharedCheck_6900_;
                    state = 67;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_6886_);
                    crate::leanh::lean_inc(v_k_6885_);
                    crate::leanh::lean_dec(v_r_6615_);
                    v___x_6888_ = crate::leanh::lean_box(0);
                    v_isShared_6889_ = v_isSharedCheck_6900_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_6890_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_6889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6888_, 4, v_l_6614_);
                    crate::leanh::lean_ctor_set(v___x_6888_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v___x_6888_, 2, v_v_6613_);
                    crate::leanh::lean_ctor_set(v___x_6888_, 1, v_k_6612_);
                    crate::leanh::lean_ctor_set(v___x_6888_, 0, v___x_6621_);
                    v___x_6892_ = v___x_6888_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_6899_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6899_, 0, v___x_6621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6899_, 1, v_k_6612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6899_, 2, v_v_6613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6899_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6899_, 4, v_l_6614_);
                    v___x_6892_ = v_reuseFailAlloc_6899_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_6766_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6765_, 4, v_l_6614_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 2, v_v_6884_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 1, v_k_6883_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 0, v___x_6621_);
                    v___x_6894_ = v___x_6765_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_6898_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6898_, 0, v___x_6621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6898_, 1, v_k_6883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6898_, 2, v_v_6884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6898_, 3, v_l_6614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6898_, 4, v_l_6614_);
                    v___x_6894_ = v_reuseFailAlloc_6898_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_6882_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6881_, 4, v___x_6894_);
                    crate::leanh::lean_ctor_set(v___x_6881_, 3, v___x_6892_);
                    crate::leanh::lean_ctor_set(v___x_6881_, 2, v_v_6886_);
                    crate::leanh::lean_ctor_set(v___x_6881_, 1, v_k_6885_);
                    crate::leanh::lean_ctor_set(v___x_6881_, 0, v___x_6890_);
                    v___x_6896_ = v___x_6881_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_6897_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6897_, 0, v___x_6890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6897_, 1, v_k_6885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6897_, 2, v_v_6886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6897_, 3, v___x_6892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6897_, 4, v___x_6894_);
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
                v_size_6941_ = crate::leanh::lean_ctor_get(v_l_6928_, 0);
                v_k_6942_ = crate::leanh::lean_ctor_get(v_l_6928_, 1);
                v_v_6943_ = crate::leanh::lean_ctor_get(v_l_6928_, 2);
                v_l_6944_ = crate::leanh::lean_ctor_get(v_l_6928_, 3);
                v_r_6945_ = crate::leanh::lean_ctor_get(v_l_6928_, 4);
                v_size_6946_ = crate::leanh::lean_ctor_get(v_r_6929_, 0);
                v___x_6947_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6948_ = lean_nat_mul(v___x_6947_, v_size_6946_);
                v___x_6949_ = lean_nat_dec_lt(v_size_6941_, v___x_6948_);
                crate::leanh::lean_dec(v___x_6948_);
                if v___x_6949_ == 0 {
                    crate::leanh::lean_inc(v_r_6945_);
                    crate::leanh::lean_inc(v_l_6944_);
                    crate::leanh::lean_inc(v_v_6943_);
                    crate::leanh::lean_inc(v_k_6942_);
                    v_isSharedCheck_6977_ = (!crate::leanh::lean_is_exclusive(v_l_6928_)) as u8;
                    if v_isSharedCheck_6977_ == 0 {
                        v_unused_6978_ = crate::leanh::lean_ctor_get(v_l_6928_, 4);
                        crate::leanh::lean_dec(v_unused_6978_);
                        v_unused_6979_ = crate::leanh::lean_ctor_get(v_l_6928_, 3);
                        crate::leanh::lean_dec(v_unused_6979_);
                        v_unused_6980_ = crate::leanh::lean_ctor_get(v_l_6928_, 2);
                        crate::leanh::lean_dec(v_unused_6980_);
                        v_unused_6981_ = crate::leanh::lean_ctor_get(v_l_6928_, 1);
                        crate::leanh::lean_dec(v_unused_6981_);
                        v_unused_6982_ = crate::leanh::lean_ctor_get(v_l_6928_, 0);
                        crate::leanh::lean_dec(v_unused_6982_);
                        v___x_6951_ = v_l_6928_;
                        v_isShared_6952_ = v_isSharedCheck_6977_;
                        state = 74;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_6928_);
                        v___x_6951_ = crate::leanh::lean_box(0);
                        v_isShared_6952_ = v_isSharedCheck_6977_;
                        state = 74;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6443_);
                    v___x_6983_ = lean_nat_add(v___x_6923_, v_size_6924_);
                    crate::leanh::lean_dec(v_size_6924_);
                    v___x_6984_ = lean_nat_add(v___x_6983_, v_size_6925_);
                    crate::leanh::lean_dec(v_size_6925_);
                    v___x_6985_ = lean_nat_add(v___x_6983_, v_size_6941_);
                    crate::leanh::lean_dec(v___x_6983_);
                    crate::leanh::lean_inc_ref(v_impl_6922_);
                    if v_isShared_6940_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6939_, 4, v_l_6928_);
                        crate::leanh::lean_ctor_set(v___x_6939_, 3, v_impl_6922_);
                        crate::leanh::lean_ctor_set(v___x_6939_, 2, v_v_6439_);
                        crate::leanh::lean_ctor_set(v___x_6939_, 1, v_k_6438_);
                        crate::leanh::lean_ctor_set(v___x_6939_, 0, v___x_6985_);
                        v___x_6987_ = v___x_6939_;
                        state = 80;
                        continue;
                    } else {
                        v_reuseFailAlloc_7000_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7000_, 0, v___x_6985_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7000_, 1, v_k_6438_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7000_, 2, v_v_6439_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7000_, 3, v_impl_6922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7000_, 4, v_l_6928_);
                        v___x_6987_ = v_reuseFailAlloc_7000_;
                        state = 80;
                        continue;
                    }
                }
            }
            74 => {
                v___x_6953_ = lean_nat_add(v___x_6923_, v_size_6924_);
                crate::leanh::lean_dec(v_size_6924_);
                v___x_6954_ = lean_nat_add(v___x_6953_, v_size_6925_);
                crate::leanh::lean_dec(v_size_6925_);
                if crate::leanh::lean_obj_tag(v_l_6944_) == 0 {
                    v_size_6975_ = crate::leanh::lean_ctor_get(v_l_6944_, 0);
                    crate::leanh::lean_inc(v_size_6975_);
                    v___y_6967_ = v_size_6975_;
                    state = 78;
                    continue;
                } else {
                    v___x_6976_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6967_ = v___x_6976_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_6959_ = lean_nat_add(v___y_6956_, v___y_6958_);
                crate::leanh::lean_dec(v___y_6958_);
                crate::leanh::lean_dec(v___y_6956_);
                if v_isShared_6952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6951_, 4, v_r_6929_);
                    crate::leanh::lean_ctor_set(v___x_6951_, 3, v_r_6945_);
                    crate::leanh::lean_ctor_set(v___x_6951_, 2, v_v_6927_);
                    crate::leanh::lean_ctor_set(v___x_6951_, 1, v_k_6926_);
                    crate::leanh::lean_ctor_set(v___x_6951_, 0, v___x_6959_);
                    v___x_6961_ = v___x_6951_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_6965_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6965_, 0, v___x_6959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6965_, 1, v_k_6926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6965_, 2, v_v_6927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6965_, 3, v_r_6945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6965_, 4, v_r_6929_);
                    v___x_6961_ = v_reuseFailAlloc_6965_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_6940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6939_, 4, v___x_6961_);
                    crate::leanh::lean_ctor_set(v___x_6939_, 3, v___y_6957_);
                    crate::leanh::lean_ctor_set(v___x_6939_, 2, v_v_6943_);
                    crate::leanh::lean_ctor_set(v___x_6939_, 1, v_k_6942_);
                    crate::leanh::lean_ctor_set(v___x_6939_, 0, v___x_6954_);
                    v___x_6963_ = v___x_6939_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_6964_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6964_, 0, v___x_6954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6964_, 1, v_k_6942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6964_, 2, v_v_6943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6964_, 3, v___y_6957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6964_, 4, v___x_6961_);
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
                crate::leanh::lean_dec(v___y_6967_);
                crate::leanh::lean_dec(v___x_6953_);
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v_l_6944_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v_impl_6922_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_6968_);
                    v___x_6970_ = v___x_6443_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_6974_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6974_, 0, v___x_6968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6974_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6974_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6974_, 3, v_impl_6922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6974_, 4, v_l_6944_);
                    v___x_6970_ = v_reuseFailAlloc_6974_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_6971_ = lean_nat_add(v___x_6923_, v_size_6946_);
                if crate::leanh::lean_obj_tag(v_r_6945_) == 0 {
                    v_size_6972_ = crate::leanh::lean_ctor_get(v_r_6945_, 0);
                    crate::leanh::lean_inc(v_size_6972_);
                    v___y_6956_ = v___x_6971_;
                    v___y_6957_ = v___x_6970_;
                    v___y_6958_ = v_size_6972_;
                    state = 75;
                    continue;
                } else {
                    v___x_6973_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_6956_ = v___x_6971_;
                    v___y_6957_ = v___x_6970_;
                    v___y_6958_ = v___x_6973_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_6994_ = (!crate::leanh::lean_is_exclusive(v_impl_6922_)) as u8;
                if v_isSharedCheck_6994_ == 0 {
                    v_unused_6995_ = crate::leanh::lean_ctor_get(v_impl_6922_, 4);
                    crate::leanh::lean_dec(v_unused_6995_);
                    v_unused_6996_ = crate::leanh::lean_ctor_get(v_impl_6922_, 3);
                    crate::leanh::lean_dec(v_unused_6996_);
                    v_unused_6997_ = crate::leanh::lean_ctor_get(v_impl_6922_, 2);
                    crate::leanh::lean_dec(v_unused_6997_);
                    v_unused_6998_ = crate::leanh::lean_ctor_get(v_impl_6922_, 1);
                    crate::leanh::lean_dec(v_unused_6998_);
                    v_unused_6999_ = crate::leanh::lean_ctor_get(v_impl_6922_, 0);
                    crate::leanh::lean_dec(v_unused_6999_);
                    v___x_6989_ = v_impl_6922_;
                    v_isShared_6990_ = v_isSharedCheck_6994_;
                    state = 81;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_6922_);
                    v___x_6989_ = crate::leanh::lean_box(0);
                    v_isShared_6990_ = v_isSharedCheck_6994_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_6990_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6989_, 4, v_r_6929_);
                    crate::leanh::lean_ctor_set(v___x_6989_, 3, v___x_6987_);
                    crate::leanh::lean_ctor_set(v___x_6989_, 2, v_v_6927_);
                    crate::leanh::lean_ctor_set(v___x_6989_, 1, v_k_6926_);
                    crate::leanh::lean_ctor_set(v___x_6989_, 0, v___x_6984_);
                    v___x_6992_ = v___x_6989_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_6993_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6993_, 0, v___x_6984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6993_, 1, v_k_6926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6993_, 2, v_v_6927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6993_, 3, v___x_6987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6993_, 4, v_r_6929_);
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
                v_size_7020_ = crate::leanh::lean_ctor_get(v_l_7012_, 0);
                v___x_7021_ = lean_nat_add(v___x_6923_, v_size_7014_);
                crate::leanh::lean_dec(v_size_7014_);
                v___x_7022_ = lean_nat_add(v___x_6923_, v_size_7020_);
                if v_isShared_7019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7018_, 4, v_l_7012_);
                    crate::leanh::lean_ctor_set(v___x_7018_, 3, v_impl_6922_);
                    crate::leanh::lean_ctor_set(v___x_7018_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v___x_7018_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v___x_7018_, 0, v___x_7022_);
                    v___x_7024_ = v___x_7018_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_7028_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7028_, 0, v___x_7022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7028_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7028_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7028_, 3, v_impl_6922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7028_, 4, v_l_7012_);
                    v___x_7024_ = v_reuseFailAlloc_7028_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v_r_7013_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v___x_7024_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 2, v_v_7016_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 1, v_k_7015_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_7021_);
                    v___x_7026_ = v___x_6443_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_7027_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 0, v___x_7021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 1, v_k_7015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 2, v_v_7016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 3, v___x_7024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7027_, 4, v_r_7013_);
                    v___x_7026_ = v_reuseFailAlloc_7027_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_7026_;
            }
            87 => {
                v_k_7037_ = crate::leanh::lean_ctor_get(v_l_7012_, 1);
                v_v_7038_ = crate::leanh::lean_ctor_get(v_l_7012_, 2);
                v_isSharedCheck_7052_ = (!crate::leanh::lean_is_exclusive(v_l_7012_)) as u8;
                if v_isSharedCheck_7052_ == 0 {
                    v_unused_7053_ = crate::leanh::lean_ctor_get(v_l_7012_, 4);
                    crate::leanh::lean_dec(v_unused_7053_);
                    v_unused_7054_ = crate::leanh::lean_ctor_get(v_l_7012_, 3);
                    crate::leanh::lean_dec(v_unused_7054_);
                    v_unused_7055_ = crate::leanh::lean_ctor_get(v_l_7012_, 0);
                    crate::leanh::lean_dec(v_unused_7055_);
                    v___x_7040_ = v_l_7012_;
                    v_isShared_7041_ = v_isSharedCheck_7052_;
                    state = 88;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_7038_);
                    crate::leanh::lean_inc(v_k_7037_);
                    crate::leanh::lean_dec(v_l_7012_);
                    v___x_7040_ = crate::leanh::lean_box(0);
                    v_isShared_7041_ = v_isSharedCheck_7052_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                v___x_7042_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7040_, 4, v_r_7013_);
                    crate::leanh::lean_ctor_set(v___x_7040_, 3, v_r_7013_);
                    crate::leanh::lean_ctor_set(v___x_7040_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v___x_7040_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v___x_7040_, 0, v___x_6923_);
                    v___x_7044_ = v___x_7040_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_7051_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 0, v___x_6923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 3, v_r_7013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7051_, 4, v_r_7013_);
                    v___x_7044_ = v_reuseFailAlloc_7051_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                if v_isShared_7036_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7035_, 3, v_r_7013_);
                    crate::leanh::lean_ctor_set(v___x_7035_, 0, v___x_6923_);
                    v___x_7046_ = v___x_7035_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_7050_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 0, v___x_6923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 1, v_k_7032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 2, v_v_7033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 3, v_r_7013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7050_, 4, v_r_7013_);
                    v___x_7046_ = v_reuseFailAlloc_7050_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v___x_7046_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v___x_7044_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 2, v_v_7038_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 1, v_k_7037_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_7042_);
                    v___x_7048_ = v___x_6443_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_7049_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7049_, 0, v___x_7042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7049_, 1, v_k_7037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7049_, 2, v_v_7038_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7049_, 3, v___x_7044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7049_, 4, v___x_7046_);
                    v___x_7048_ = v_reuseFailAlloc_7049_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_7048_;
            }
            92 => {
                v___x_7066_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_7065_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7064_, 4, v_l_7012_);
                    crate::leanh::lean_ctor_set(v___x_7064_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v___x_7064_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v___x_7064_, 0, v___x_6923_);
                    v___x_7068_ = v___x_7064_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_7072_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7072_, 0, v___x_6923_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7072_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7072_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7072_, 3, v_l_7012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7072_, 4, v_l_7012_);
                    v___x_7068_ = v_reuseFailAlloc_7072_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v_r_7060_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v___x_7068_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 2, v_v_7062_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 1, v_k_7061_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_7066_);
                    v___x_7070_ = v___x_6443_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_7071_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7071_, 0, v___x_7066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7071_, 1, v_k_7061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7071_, 2, v_v_7062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7071_, 3, v___x_7068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7071_, 4, v_r_7060_);
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
                    crate::leanh::lean_ctor_set(v___x_7081_, 3, v_r_7060_);
                    v___x_7084_ = v___x_7081_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_7089_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 0, v_size_7077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 1, v_k_7078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 2, v_v_7079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 3, v_r_7060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7089_, 4, v_r_7060_);
                    v___x_7084_ = v_reuseFailAlloc_7089_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                v___x_7085_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_6444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6443_, 4, v___x_7084_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 3, v_r_7060_);
                    crate::leanh::lean_ctor_set(v___x_6443_, 0, v___x_7085_);
                    v___x_7087_ = v___x_6443_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_7088_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 0, v___x_7085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 1, v_k_6438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 2, v_v_6439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 3, v_r_7060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 4, v___x_7084_);
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
    mut v_k_7098_: *mut crate::leanh::LeanObject,
    mut v_t_7099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7100_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_7098_, v_t_7099_);
    crate::leanh::lean_dec(v_k_7098_);
    return v_res_7100_;
}
pub unsafe fn l_Lean_IR_LocalContext_eraseJoinPointDecl(
    mut v_ctx_7101_: *mut crate::leanh::LeanObject,
    mut v_j_7102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7103_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_j_7102_, v_ctx_7101_);
    return v___x_7103_;
}
pub unsafe fn l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(
    mut v_ctx_7104_: *mut crate::leanh::LeanObject,
    mut v_j_7105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7106_ = l_Lean_IR_LocalContext_eraseJoinPointDecl(v_ctx_7104_, v_j_7105_);
    crate::leanh::lean_dec(v_j_7105_);
    return v_res_7106_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(
    mut v_00_u03b2_7107_: *mut crate::leanh::LeanObject,
    mut v_k_7108_: *mut crate::leanh::LeanObject,
    mut v_t_7109_: *mut crate::leanh::LeanObject,
    mut v_h_7110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7111_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(v_k_7108_, v_t_7109_);
    return v___x_7111_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(
    mut v_00_u03b2_7112_: *mut crate::leanh::LeanObject,
    mut v_k_7113_: *mut crate::leanh::LeanObject,
    mut v_t_7114_: *mut crate::leanh::LeanObject,
    mut v_h_7115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7116_ =
        l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(
            v_00_u03b2_7112_,
            v_k_7113_,
            v_t_7114_,
            v_h_7115_,
        );
    crate::leanh::lean_dec(v_k_7113_);
    return v_res_7116_;
}
pub unsafe fn l_Lean_IR_LocalContext_getType(
    mut v_ctx_7117_: *mut crate::leanh::LeanObject,
    mut v_x_7118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7123_: u8 = 0;
    let mut v_a_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7133_: u8 = 0;
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7119_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_7117_, v_x_7118_);
                if crate::leanh::lean_obj_tag(v___x_7119_) == 1 {
                    v_val_7120_ = crate::leanh::lean_ctor_get(v___x_7119_, 0);
                    v_isSharedCheck_7133_ = (!crate::leanh::lean_is_exclusive(v___x_7119_)) as u8;
                    if v_isSharedCheck_7133_ == 0 {
                        v___x_7122_ = v___x_7119_;
                        v_isShared_7123_ = v_isSharedCheck_7133_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7120_);
                        crate::leanh::lean_dec(v___x_7119_);
                        v___x_7122_ = crate::leanh::lean_box(0);
                        v_isShared_7123_ = v_isSharedCheck_7133_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7119_);
                    v___x_7134_ = crate::leanh::lean_box(0);
                    return v___x_7134_;
                }
            }
            1 => match crate::leanh::lean_obj_tag(v_val_7120_) {
                0 => {
                    v_a_7124_ = crate::leanh::lean_ctor_get(v_val_7120_, 0);
                    crate::leanh::lean_inc(v_a_7124_);
                    crate::leanh::lean_dec_ref_known(v_val_7120_, 1);
                    if v_isShared_7123_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7122_, 0, v_a_7124_);
                        v___x_7126_ = v___x_7122_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7127_, 0, v_a_7124_);
                        v___x_7126_ = v_reuseFailAlloc_7127_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_a_7128_ = crate::leanh::lean_ctor_get(v_val_7120_, 0);
                    crate::leanh::lean_inc(v_a_7128_);
                    crate::leanh::lean_dec_ref_known(v_val_7120_, 2);
                    if v_isShared_7123_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7122_, 0, v_a_7128_);
                        v___x_7130_ = v___x_7122_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7131_, 0, v_a_7128_);
                        v___x_7130_ = v_reuseFailAlloc_7131_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_del_object(v___x_7122_);
                    crate::leanh::lean_dec(v_val_7120_);
                    v___x_7132_ = crate::leanh::lean_box(0);
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
    mut v_ctx_7135_: *mut crate::leanh::LeanObject,
    mut v_x_7136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7137_ = l_Lean_IR_LocalContext_getType(v_ctx_7135_, v_x_7136_);
    crate::leanh::lean_dec(v_x_7136_);
    crate::leanh::lean_dec(v_ctx_7135_);
    return v_res_7137_;
}
pub unsafe fn l_Lean_IR_LocalContext_getValue(
    mut v_ctx_7138_: *mut crate::leanh::LeanObject,
    mut v_x_7139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7144_: u8 = 0;
    let mut v_a_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7150_: u8 = 0;
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_ctx_7138_, v_x_7139_);
                if crate::leanh::lean_obj_tag(v___x_7140_) == 1 {
                    v_val_7141_ = crate::leanh::lean_ctor_get(v___x_7140_, 0);
                    v_isSharedCheck_7150_ = (!crate::leanh::lean_is_exclusive(v___x_7140_)) as u8;
                    if v_isSharedCheck_7150_ == 0 {
                        v___x_7143_ = v___x_7140_;
                        v_isShared_7144_ = v_isSharedCheck_7150_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7141_);
                        crate::leanh::lean_dec(v___x_7140_);
                        v___x_7143_ = crate::leanh::lean_box(0);
                        v_isShared_7144_ = v_isSharedCheck_7150_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7140_);
                    v___x_7151_ = crate::leanh::lean_box(0);
                    return v___x_7151_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_7141_) == 1 {
                    v_a_7145_ = crate::leanh::lean_ctor_get(v_val_7141_, 1);
                    crate::leanh::lean_inc_ref(v_a_7145_);
                    crate::leanh::lean_dec_ref_known(v_val_7141_, 2);
                    if v_isShared_7144_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7143_, 0, v_a_7145_);
                        v___x_7147_ = v___x_7143_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7148_, 0, v_a_7145_);
                        v___x_7147_ = v_reuseFailAlloc_7148_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7143_);
                    crate::leanh::lean_dec(v_val_7141_);
                    v___x_7149_ = crate::leanh::lean_box(0);
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
    mut v_ctx_7152_: *mut crate::leanh::LeanObject,
    mut v_x_7153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7154_ = l_Lean_IR_LocalContext_getValue(v_ctx_7152_, v_x_7153_);
    crate::leanh::lean_dec(v_x_7153_);
    crate::leanh::lean_dec(v_ctx_7152_);
    return v_res_7154_;
}
pub unsafe fn l_Lean_IR_VarId_alphaEqv(
    mut v_00_u03c1_7155_: *mut crate::leanh::LeanObject,
    mut v_v_u2081_7156_: *mut crate::leanh::LeanObject,
    mut v_v_u2082_7157_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7158_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_IR_LocalContext_isJP_spec__0___redArg(v_00_u03c1_7155_, v_v_u2081_7156_);
    if crate::leanh::lean_obj_tag(v___x_7158_) == 0 {
        let mut v___x_7159_: u8 = 0;
        v___x_7159_ = lean_nat_dec_eq(v_v_u2081_7156_, v_v_u2082_7157_);
        return v___x_7159_;
    } else {
        let mut v_val_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7161_: u8 = 0;
        v_val_7160_ = crate::leanh::lean_ctor_get(v___x_7158_, 0);
        crate::leanh::lean_inc(v_val_7160_);
        crate::leanh::lean_dec_ref_known(v___x_7158_, 1);
        v___x_7161_ = lean_nat_dec_eq(v_val_7160_, v_v_u2082_7157_);
        crate::leanh::lean_dec(v_val_7160_);
        return v___x_7161_;
    }
}
pub unsafe fn l_Lean_IR_VarId_alphaEqv___boxed(
    mut v_00_u03c1_7162_: *mut crate::leanh::LeanObject,
    mut v_v_u2081_7163_: *mut crate::leanh::LeanObject,
    mut v_v_u2082_7164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7165_: u8 = 0;
    let mut v_r_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7165_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7162_, v_v_u2081_7163_, v_v_u2082_7164_);
    crate::leanh::lean_dec(v_v_u2082_7164_);
    crate::leanh::lean_dec(v_v_u2081_7163_);
    crate::leanh::lean_dec(v_00_u03c1_7162_);
    v_r_7166_ = crate::leanh::lean_box((v_res_7165_) as usize);
    return v_r_7166_;
}
pub unsafe fn l_Lean_IR_Arg_alphaEqv(
    mut v_00_u03c1_7169_: *mut crate::leanh::LeanObject,
    mut v_x_7170_: *mut crate::leanh::LeanObject,
    mut v_x_7171_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_7170_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_7171_) == 0 {
            let mut v_id_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_7174_: u8 = 0;
            v_id_7172_ = crate::leanh::lean_ctor_get(v_x_7170_, 0);
            v_id_7173_ = crate::leanh::lean_ctor_get(v_x_7171_, 0);
            v___x_7174_ = l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7169_, v_id_7172_, v_id_7173_);
            return v___x_7174_;
        } else {
            let mut v___x_7175_: u8 = 0;
            v___x_7175_ = 0;
            return v___x_7175_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_7171_) == 1 {
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
    mut v_00_u03c1_7178_: *mut crate::leanh::LeanObject,
    mut v_x_7179_: *mut crate::leanh::LeanObject,
    mut v_x_7180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7181_: u8 = 0;
    let mut v_r_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7181_ = l_Lean_IR_Arg_alphaEqv(v_00_u03c1_7178_, v_x_7179_, v_x_7180_);
    crate::leanh::lean_dec(v_x_7180_);
    crate::leanh::lean_dec(v_x_7179_);
    crate::leanh::lean_dec(v_00_u03c1_7178_);
    v_r_7182_ = crate::leanh::lean_box((v_res_7181_) as usize);
    return v_r_7182_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(
    mut v_00_u03c1_7185_: *mut crate::leanh::LeanObject,
    mut v_xs_7186_: *mut crate::leanh::LeanObject,
    mut v_ys_7187_: *mut crate::leanh::LeanObject,
    mut v_x_7188_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7190_: u8 = 0;
    let mut v_one_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7189_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_7190_ = lean_nat_dec_eq(v_x_7188_, v_zero_7189_);
                if v_isZero_7190_ == 1 {
                    crate::leanh::lean_dec(v_x_7188_);
                    return v_isZero_7190_;
                } else {
                    v_one_7191_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_7192_ = lean_nat_sub(v_x_7188_, v_one_7191_);
                    crate::leanh::lean_dec(v_x_7188_);
                    v___x_7193_ = lean_array_fget_borrowed(v_xs_7186_, v_n_7192_);
                    v___x_7194_ = lean_array_fget_borrowed(v_ys_7187_, v_n_7192_);
                    v___x_7195_ =
                        l_Lean_IR_Arg_alphaEqv(v_00_u03c1_7185_, v___x_7193_, v___x_7194_);
                    if v___x_7195_ == 0 {
                        crate::leanh::lean_dec(v_n_7192_);
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
    mut v_00_u03c1_7197_: *mut crate::leanh::LeanObject,
    mut v_xs_7198_: *mut crate::leanh::LeanObject,
    mut v_ys_7199_: *mut crate::leanh::LeanObject,
    mut v_x_7200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7201_: u8 = 0;
    let mut v_r_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7201_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0___redArg(
        v_00_u03c1_7197_,
        v_xs_7198_,
        v_ys_7199_,
        v_x_7200_,
    );
    crate::leanh::lean_dec_ref(v_ys_7199_);
    crate::leanh::lean_dec_ref(v_xs_7198_);
    crate::leanh::lean_dec(v_00_u03c1_7197_);
    v_r_7202_ = crate::leanh::lean_box((v_res_7201_) as usize);
    return v_r_7202_;
}
pub unsafe fn l_Lean_IR_args_alphaEqv(
    mut v_00_u03c1_7203_: *mut crate::leanh::LeanObject,
    mut v_args_u2081_7204_: *mut crate::leanh::LeanObject,
    mut v_args_u2082_7205_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03c1_7210_: *mut crate::leanh::LeanObject,
    mut v_args_u2081_7211_: *mut crate::leanh::LeanObject,
    mut v_args_u2082_7212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7213_: u8 = 0;
    let mut v_r_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7213_ = l_Lean_IR_args_alphaEqv(v_00_u03c1_7210_, v_args_u2081_7211_, v_args_u2082_7212_);
    crate::leanh::lean_dec_ref(v_args_u2082_7212_);
    crate::leanh::lean_dec_ref(v_args_u2081_7211_);
    crate::leanh::lean_dec(v_00_u03c1_7210_);
    v_r_7214_ = crate::leanh::lean_box((v_res_7213_) as usize);
    return v_r_7214_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(
    mut v_00_u03c1_7215_: *mut crate::leanh::LeanObject,
    mut v_xs_7216_: *mut crate::leanh::LeanObject,
    mut v_ys_7217_: *mut crate::leanh::LeanObject,
    mut v_hsz_7218_: *mut crate::leanh::LeanObject,
    mut v_x_7219_: *mut crate::leanh::LeanObject,
    mut v_x_7220_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03c1_7222_: *mut crate::leanh::LeanObject,
    mut v_xs_7223_: *mut crate::leanh::LeanObject,
    mut v_ys_7224_: *mut crate::leanh::LeanObject,
    mut v_hsz_7225_: *mut crate::leanh::LeanObject,
    mut v_x_7226_: *mut crate::leanh::LeanObject,
    mut v_x_7227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7228_: u8 = 0;
    let mut v_r_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7228_ = l_Array_isEqvAux___at___00Lean_IR_args_alphaEqv_spec__0(
        v_00_u03c1_7222_,
        v_xs_7223_,
        v_ys_7224_,
        v_hsz_7225_,
        v_x_7226_,
        v_x_7227_,
    );
    crate::leanh::lean_dec_ref(v_ys_7224_);
    crate::leanh::lean_dec_ref(v_xs_7223_);
    crate::leanh::lean_dec(v_00_u03c1_7222_);
    v_r_7229_ = crate::leanh::lean_box((v_res_7228_) as usize);
    return v_r_7229_;
}
pub unsafe fn l_Lean_IR_Expr_alphaEqv(
    mut v_00_u03c1_7232_: *mut crate::leanh::LeanObject,
    mut v_x_7233_: *mut crate::leanh::LeanObject,
    mut v_x_7234_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_n_u2081_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_u2081_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_u2082_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_u2082_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: u8 = 0;
    let mut v___x_7241_: u8 = 0;
    let mut v_c_u2081_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_u2081_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_u2082_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: u8 = 0;
    let mut v___x_7248_: u8 = 0;
    let mut v_i_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7253_: u8 = 0;
    let mut v___x_7254_: u8 = 0;
    let mut v___x_7255_: u8 = 0;
    let mut v_n_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: u8 = 0;
    let mut v_x_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_7263_: u8 = 0;
    let mut v_ys_7264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_updtHeader_7267_: u8 = 0;
    let mut v_ys_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7270_: u8 = 0;
    let mut v___x_7271_: u8 = 0;
    let mut v___x_7272_: u8 = 0;
    let mut v___x_7273_: u8 = 0;
    let mut v___x_7274_: u8 = 0;
    let mut v___x_7275_: u8 = 0;
    let mut v_i_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: u8 = 0;
    let mut v_i_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: u8 = 0;
    let mut v_n_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7293_: u8 = 0;
    let mut v___x_7294_: u8 = 0;
    let mut v___x_7295_: u8 = 0;
    let mut v___x_7296_: u8 = 0;
    let mut v___x_7297_: u8 = 0;
    let mut v_c_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: u8 = 0;
    let mut v_c_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: u8 = 0;
    let mut v_x_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: u8 = 0;
    let mut v___x_7313_: u8 = 0;
    let mut v___x_7314_: u8 = 0;
    let mut v_ty_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: u8 = 0;
    let mut v___x_7320_: u8 = 0;
    let mut v___x_7321_: u8 = 0;
    let mut v_x_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: u8 = 0;
    let mut v___x_7325_: u8 = 0;
    let mut v_v_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: u8 = 0;
    let mut v___x_7329_: u8 = 0;
    let mut v_x_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: u8 = 0;
    let mut v___x_7333_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_7233_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 0 {
                        v_i_7249_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_ys_7250_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_i_7251_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_ys_7252_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 1 {
                        v_n_7256_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_x_7257_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_n_7258_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_x_7259_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 2 {
                        v_x_7261_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_i_7262_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_updtHeader_7263_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7233_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_ys_7264_ = crate::leanh::lean_ctor_get(v_x_7233_, 2);
                        v_x_7265_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_i_7266_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
                        v_updtHeader_7267_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7234_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_ys_7268_ = crate::leanh::lean_ctor_get(v_x_7234_, 2);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 3 {
                        v_i_7276_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_x_7277_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_i_7278_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_x_7279_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 4 {
                        v_i_7281_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_x_7282_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_i_7283_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_x_7284_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 5 {
                        v_n_7286_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_offset_7287_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_x_7288_ = crate::leanh::lean_ctor_get(v_x_7233_, 2);
                        v_n_7289_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_offset_7290_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
                        v_x_7291_ = crate::leanh::lean_ctor_get(v_x_7234_, 2);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 6 {
                        v_c_7298_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_ys_7299_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_c_7300_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_ys_7301_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 7 {
                        v_c_7303_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_ys_7304_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_c_7305_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_ys_7306_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 8 {
                        v_x_7308_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_ys_7309_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_x_7310_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_ys_7311_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 9 {
                        v_ty_7315_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_x_7316_ = crate::leanh::lean_ctor_get(v_x_7233_, 1);
                        v_ty_7317_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v_x_7318_ = crate::leanh::lean_ctor_get(v_x_7234_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 10 {
                        v_x_7322_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_x_7323_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v___x_7324_ =
                            l_Lean_IR_VarId_alphaEqv(v_00_u03c1_7232_, v_x_7322_, v_x_7323_);
                        return v___x_7324_;
                    } else {
                        v___x_7325_ = 0;
                        return v___x_7325_;
                    }
                }
                11 => {
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 11 {
                        v_v_7326_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_v_7327_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
                        v___x_7328_ = l_Lean_IR_instBEqLitVal_beq(v_v_7326_, v_v_7327_);
                        return v___x_7328_;
                    } else {
                        v___x_7329_ = 0;
                        return v___x_7329_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_7234_) == 12 {
                        v_x_7330_ = crate::leanh::lean_ctor_get(v_x_7233_, 0);
                        v_x_7331_ = crate::leanh::lean_ctor_get(v_x_7234_, 0);
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
    mut v_00_u03c1_7334_: *mut crate::leanh::LeanObject,
    mut v_x_7335_: *mut crate::leanh::LeanObject,
    mut v_x_7336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7337_: u8 = 0;
    let mut v_r_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7337_ = l_Lean_IR_Expr_alphaEqv(v_00_u03c1_7334_, v_x_7335_, v_x_7336_);
    crate::leanh::lean_dec_ref(v_x_7336_);
    crate::leanh::lean_dec_ref(v_x_7335_);
    crate::leanh::lean_dec(v_00_u03c1_7334_);
    v_r_7338_ = crate::leanh::lean_box((v_res_7337_) as usize);
    return v_r_7338_;
}
pub unsafe fn l_Lean_IR_addVarRename(
    mut v_00_u03c1_7341_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_7342_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_7343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7344_: u8 = 0;
    v___x_7344_ = lean_nat_dec_eq(v_x_u2081_7342_, v_x_u2082_7343_);
    if v___x_7344_ == 0 {
        let mut v___x_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7345_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_IR_mkIndexSet_spec__1___redArg(
                v_x_u2081_7342_,
                v_x_u2082_7343_,
                v_00_u03c1_7341_,
            );
        return v___x_7345_;
    } else {
        crate::leanh::lean_dec(v_x_u2082_7343_);
        crate::leanh::lean_dec(v_x_u2081_7342_);
        return v_00_u03c1_7341_;
    }
}
pub unsafe fn l_Lean_IR_addParamRename(
    mut v_00_u03c1_7346_: *mut crate::leanh::LeanObject,
    mut v_p_u2081_7347_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_7348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_7350_: u8 = 0;
    let mut v_ty_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_borrow_7353_: u8 = 0;
    let mut v_ty_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7356_: u8 = 0;
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: u8 = 0;
    let mut v___x_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_7349_ = crate::leanh::lean_ctor_get(v_p_u2081_7347_, 0);
                crate::leanh::lean_inc(v_x_7349_);
                v_borrow_7350_ = crate::leanh::lean_ctor_get_uint8(
                    v_p_u2081_7347_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_ty_7351_ = crate::leanh::lean_ctor_get(v_p_u2081_7347_, 1);
                crate::leanh::lean_inc(v_ty_7351_);
                crate::leanh::lean_dec_ref(v_p_u2081_7347_);
                v_x_7352_ = crate::leanh::lean_ctor_get(v_p_u2082_7348_, 0);
                crate::leanh::lean_inc(v_x_7352_);
                v_borrow_7353_ = crate::leanh::lean_ctor_get_uint8(
                    v_p_u2082_7348_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_ty_7354_ = crate::leanh::lean_ctor_get(v_p_u2082_7348_, 1);
                crate::leanh::lean_inc(v_ty_7354_);
                crate::leanh::lean_dec_ref(v_p_u2082_7348_);
                v___x_7360_ = l_Lean_IR_instBEqIRType_beq(v_ty_7351_, v_ty_7354_);
                crate::leanh::lean_dec(v_ty_7354_);
                crate::leanh::lean_dec(v_ty_7351_);
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
                            crate::leanh::lean_dec(v_x_7352_);
                            crate::leanh::lean_dec(v_x_7349_);
                            crate::leanh::lean_dec(v_00_u03c1_7346_);
                            v___x_7361_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v_x_7352_);
                    crate::leanh::lean_dec(v_x_7349_);
                    crate::leanh::lean_dec(v_00_u03c1_7346_);
                    v___x_7357_ = crate::leanh::lean_box(0);
                    return v___x_7357_;
                } else {
                    v___x_7358_ = l_Lean_IR_addVarRename(v_00_u03c1_7346_, v_x_7349_, v_x_7352_);
                    v___x_7359_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7359_, 0, v___x_7358_);
                    return v___x_7359_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(
    mut v_upperBound_7362_: *mut crate::leanh::LeanObject,
    mut v_ps_u2081_7363_: *mut crate::leanh::LeanObject,
    mut v_ps_u2082_7364_: *mut crate::leanh::LeanObject,
    mut v_a_7365_: *mut crate::leanh::LeanObject,
    mut v_b_7366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7367_: u8 = 0;
    let mut v___x_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7367_ = lean_nat_dec_lt(v_a_7365_, v_upperBound_7362_);
                if v___x_7367_ == 0 {
                    crate::leanh::lean_dec(v_a_7365_);
                    v___x_7368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7368_, 0, v_b_7366_);
                    return v___x_7368_;
                } else {
                    v___x_7369_ = l_Lean_IR_instInhabitedParam_default;
                    v___x_7370_ = lean_array_get_borrowed(v___x_7369_, v_ps_u2081_7363_, v_a_7365_);
                    v___x_7371_ = lean_array_get_borrowed(v___x_7369_, v_ps_u2082_7364_, v_a_7365_);
                    crate::leanh::lean_inc(v___x_7371_);
                    crate::leanh::lean_inc(v___x_7370_);
                    v___x_7372_ = l_Lean_IR_addParamRename(v_b_7366_, v___x_7370_, v___x_7371_);
                    if crate::leanh::lean_obj_tag(v___x_7372_) == 0 {
                        crate::leanh::lean_dec(v_a_7365_);
                        return v___x_7372_;
                    } else {
                        v_val_7373_ = crate::leanh::lean_ctor_get(v___x_7372_, 0);
                        crate::leanh::lean_inc(v_val_7373_);
                        crate::leanh::lean_dec_ref_known(v___x_7372_, 1);
                        v___x_7374_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7375_ = lean_nat_add(v_a_7365_, v___x_7374_);
                        crate::leanh::lean_dec(v_a_7365_);
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
    mut v_upperBound_7377_: *mut crate::leanh::LeanObject,
    mut v_ps_u2081_7378_: *mut crate::leanh::LeanObject,
    mut v_ps_u2082_7379_: *mut crate::leanh::LeanObject,
    mut v_a_7380_: *mut crate::leanh::LeanObject,
    mut v_b_7381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7382_ = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0___redArg(
        v_upperBound_7377_,
        v_ps_u2081_7378_,
        v_ps_u2082_7379_,
        v_a_7380_,
        v_b_7381_,
    );
    crate::leanh::lean_dec_ref(v_ps_u2082_7379_);
    crate::leanh::lean_dec_ref(v_ps_u2081_7378_);
    crate::leanh::lean_dec(v_upperBound_7377_);
    return v_res_7382_;
}
pub unsafe fn l_Lean_IR_addParamsRename(
    mut v_00_u03c1_7383_: *mut crate::leanh::LeanObject,
    mut v_ps_u2081_7384_: *mut crate::leanh::LeanObject,
    mut v_ps_u2082_7385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: u8 = 0;
    v___x_7386_ = lean_array_get_size(v_ps_u2081_7384_);
    v___x_7387_ = lean_array_get_size(v_ps_u2082_7385_);
    v___x_7388_ = lean_nat_dec_eq(v___x_7386_, v___x_7387_);
    if v___x_7388_ == 0 {
        let mut v___x_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_00_u03c1_7383_);
        v___x_7389_ = crate::leanh::lean_box(0);
        return v___x_7389_;
    } else {
        let mut v___x_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_7390_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_00_u03c1_7392_: *mut crate::leanh::LeanObject,
    mut v_ps_u2081_7393_: *mut crate::leanh::LeanObject,
    mut v_ps_u2082_7394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7395_ = l_Lean_IR_addParamsRename(v_00_u03c1_7392_, v_ps_u2081_7393_, v_ps_u2082_7394_);
    crate::leanh::lean_dec_ref(v_ps_u2082_7394_);
    crate::leanh::lean_dec_ref(v_ps_u2081_7393_);
    return v_res_7395_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_IR_addParamsRename_spec__0(
    mut v_upperBound_7396_: *mut crate::leanh::LeanObject,
    mut v_ps_u2081_7397_: *mut crate::leanh::LeanObject,
    mut v_ps_u2082_7398_: *mut crate::leanh::LeanObject,
    mut v_inst_7399_: *mut crate::leanh::LeanObject,
    mut v_R_7400_: *mut crate::leanh::LeanObject,
    mut v_a_7401_: *mut crate::leanh::LeanObject,
    mut v_b_7402_: *mut crate::leanh::LeanObject,
    mut v_c_7403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_upperBound_7405_: *mut crate::leanh::LeanObject,
    mut v_ps_u2081_7406_: *mut crate::leanh::LeanObject,
    mut v_ps_u2082_7407_: *mut crate::leanh::LeanObject,
    mut v_inst_7408_: *mut crate::leanh::LeanObject,
    mut v_R_7409_: *mut crate::leanh::LeanObject,
    mut v_a_7410_: *mut crate::leanh::LeanObject,
    mut v_b_7411_: *mut crate::leanh::LeanObject,
    mut v_c_7412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_ps_u2082_7407_);
    crate::leanh::lean_dec_ref(v_ps_u2081_7406_);
    crate::leanh::lean_dec(v_upperBound_7405_);
    return v_res_7413_;
}
pub unsafe fn l_Lean_IR_FnBody_alphaEqv(
    mut v_x_7414_: *mut crate::leanh::LeanObject,
    mut v_x_7415_: *mut crate::leanh::LeanObject,
    mut v_x_7416_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_7418_: u8 = 0;
    let mut v___y_7419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7421_: u8 = 0;
    let mut v___y_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7426_: u8 = 0;
    let mut v___y_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7429_: u8 = 0;
    let mut v___y_7430_: u8 = 0;
    let mut v___y_7431_: u8 = 0;
    let mut v___y_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7433_: u8 = 0;
    let mut v_00_u03c1_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_u2081_7436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_u2081_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_7438_: u8 = 0;
    let mut v_p_u2081_7439_: u8 = 0;
    let mut v_b_u2081_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_u2082_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_u2082_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_7443_: u8 = 0;
    let mut v_p_u2082_7444_: u8 = 0;
    let mut v_b_u2082_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: u8 = 0;
    let mut v___x_7447_: u8 = 0;
    let mut v_x_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7457_: u8 = 0;
    let mut v___x_7458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v___x_7461_: u8 = 0;
    let mut v___x_7462_: u8 = 0;
    let mut v_j_7463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: u8 = 0;
    let mut v_val_7473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7474_: u8 = 0;
    let mut v___x_7475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: u8 = 0;
    let mut v_x_7478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7487_: u8 = 0;
    let mut v___x_7488_: u8 = 0;
    let mut v___x_7490_: u8 = 0;
    let mut v___x_7491_: u8 = 0;
    let mut v___x_7492_: u8 = 0;
    let mut v_x_7493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7500_: u8 = 0;
    let mut v___x_7502_: u8 = 0;
    let mut v___x_7503_: u8 = 0;
    let mut v___x_7504_: u8 = 0;
    let mut v_x_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7514_: u8 = 0;
    let mut v___x_7515_: u8 = 0;
    let mut v___x_7517_: u8 = 0;
    let mut v___x_7518_: u8 = 0;
    let mut v___x_7519_: u8 = 0;
    let mut v_x_7520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: u8 = 0;
    let mut v___y_7534_: u8 = 0;
    let mut v___x_7535_: u8 = 0;
    let mut v___x_7536_: u8 = 0;
    let mut v___x_7538_: u8 = 0;
    let mut v___x_7539_: u8 = 0;
    let mut v___x_7540_: u8 = 0;
    let mut v_x_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_7543_: u8 = 0;
    let mut v_persistent_7544_: u8 = 0;
    let mut v_b_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_7548_: u8 = 0;
    let mut v_persistent_7549_: u8 = 0;
    let mut v_b_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: u8 = 0;
    let mut v_x_7552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_7554_: u8 = 0;
    let mut v_persistent_7555_: u8 = 0;
    let mut v_b_7556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_7559_: u8 = 0;
    let mut v_persistent_7560_: u8 = 0;
    let mut v_b_7561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: u8 = 0;
    let mut v_x_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7567_: u8 = 0;
    let mut v___x_7569_: u8 = 0;
    let mut v_tid_7570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tid_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cs_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7577_: u8 = 0;
    let mut v___x_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: u8 = 0;
    let mut v___x_7581_: u8 = 0;
    let mut v___x_7582_: u8 = 0;
    let mut v___x_7583_: u8 = 0;
    let mut v___x_7584_: u8 = 0;
    let mut v_x_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_7586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: u8 = 0;
    let mut v___x_7588_: u8 = 0;
    let mut v_j_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_7592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: u8 = 0;
    let mut v___x_7594_: u8 = 0;
    let mut v___x_7595_: u8 = 0;
    let mut v___x_7596_: u8 = 0;
    let mut v___x_7597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_7415_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 0 {
                        v_x_7448_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7448_);
                        v_ty_7449_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_ty_7449_);
                        v_e_7450_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc_ref(v_e_7450_);
                        v_b_7451_ = crate::leanh::lean_ctor_get(v_x_7415_, 3);
                        crate::leanh::lean_inc(v_b_7451_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        v_x_7452_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7452_);
                        v_ty_7453_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_ty_7453_);
                        v_e_7454_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc_ref(v_e_7454_);
                        v_b_7455_ = crate::leanh::lean_ctor_get(v_x_7416_, 3);
                        crate::leanh::lean_inc(v_b_7455_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7460_ = l_Lean_IR_instBEqIRType_beq(v_ty_7449_, v_ty_7453_);
                        crate::leanh::lean_dec(v_ty_7453_);
                        crate::leanh::lean_dec(v_ty_7449_);
                        if v___x_7460_ == 0 {
                            crate::leanh::lean_dec_ref(v_e_7454_);
                            crate::leanh::lean_dec_ref(v_e_7450_);
                            v___y_7457_ = v___x_7460_;
                            state = 4;
                            continue;
                        } else {
                            v___x_7461_ = l_Lean_IR_Expr_alphaEqv(v_x_7414_, v_e_7450_, v_e_7454_);
                            crate::leanh::lean_dec_ref(v_e_7454_);
                            crate::leanh::lean_dec_ref(v_e_7450_);
                            v___y_7457_ = v___x_7461_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7462_ = 0;
                        return v___x_7462_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 1 {
                        v_j_7463_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_j_7463_);
                        v_xs_7464_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc_ref(v_xs_7464_);
                        v_v_7465_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc(v_v_7465_);
                        v_b_7466_ = crate::leanh::lean_ctor_get(v_x_7415_, 3);
                        crate::leanh::lean_inc(v_b_7466_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        v_j_7467_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_j_7467_);
                        v_xs_7468_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc_ref(v_xs_7468_);
                        v_v_7469_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc(v_v_7469_);
                        v_b_7470_ = crate::leanh::lean_ctor_get(v_x_7416_, 3);
                        crate::leanh::lean_inc(v_b_7470_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 4);
                        crate::leanh::lean_inc(v_x_7414_);
                        v___x_7471_ = l_Lean_IR_addParamsRename(v_x_7414_, v_xs_7464_, v_xs_7468_);
                        crate::leanh::lean_dec_ref(v_xs_7468_);
                        crate::leanh::lean_dec_ref(v_xs_7464_);
                        if crate::leanh::lean_obj_tag(v___x_7471_) == 0 {
                            crate::leanh::lean_dec(v_b_7470_);
                            crate::leanh::lean_dec(v_v_7469_);
                            crate::leanh::lean_dec(v_j_7467_);
                            crate::leanh::lean_dec(v_b_7466_);
                            crate::leanh::lean_dec(v_v_7465_);
                            crate::leanh::lean_dec(v_j_7463_);
                            crate::leanh::lean_dec(v_x_7414_);
                            v___x_7472_ = 0;
                            return v___x_7472_;
                        } else {
                            v_val_7473_ = crate::leanh::lean_ctor_get(v___x_7471_, 0);
                            crate::leanh::lean_inc(v_val_7473_);
                            crate::leanh::lean_dec_ref_known(v___x_7471_, 1);
                            v___x_7474_ =
                                l_Lean_IR_FnBody_alphaEqv(v_val_7473_, v_v_7465_, v_v_7469_);
                            if v___x_7474_ == 0 {
                                crate::leanh::lean_dec(v_b_7470_);
                                crate::leanh::lean_dec(v_j_7467_);
                                crate::leanh::lean_dec(v_b_7466_);
                                crate::leanh::lean_dec(v_j_7463_);
                                crate::leanh::lean_dec(v_x_7414_);
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
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7477_ = 0;
                        return v___x_7477_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 2 {
                        v_x_7478_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7478_);
                        v_i_7479_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_i_7479_);
                        v_y_7480_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc(v_y_7480_);
                        v_b_7481_ = crate::leanh::lean_ctor_get(v_x_7415_, 3);
                        crate::leanh::lean_inc(v_b_7481_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        v_x_7482_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7482_);
                        v_i_7483_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_i_7483_);
                        v_y_7484_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc(v_y_7484_);
                        v_b_7485_ = crate::leanh::lean_ctor_get(v_x_7416_, 3);
                        crate::leanh::lean_inc(v_b_7485_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7490_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7478_, v_x_7482_);
                        crate::leanh::lean_dec(v_x_7482_);
                        crate::leanh::lean_dec(v_x_7478_);
                        if v___x_7490_ == 0 {
                            crate::leanh::lean_dec(v_i_7483_);
                            crate::leanh::lean_dec(v_i_7479_);
                            v___y_7487_ = v___x_7490_;
                            state = 5;
                            continue;
                        } else {
                            v___x_7491_ = lean_nat_dec_eq(v_i_7479_, v_i_7483_);
                            crate::leanh::lean_dec(v_i_7483_);
                            crate::leanh::lean_dec(v_i_7479_);
                            v___y_7487_ = v___x_7491_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7492_ = 0;
                        return v___x_7492_;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 3 {
                        v_x_7493_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7493_);
                        v_cidx_7494_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_cidx_7494_);
                        v_b_7495_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc(v_b_7495_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 3);
                        v_x_7496_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7496_);
                        v_cidx_7497_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_cidx_7497_);
                        v_b_7498_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc(v_b_7498_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 3);
                        v___x_7502_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7493_, v_x_7496_);
                        crate::leanh::lean_dec(v_x_7496_);
                        crate::leanh::lean_dec(v_x_7493_);
                        if v___x_7502_ == 0 {
                            crate::leanh::lean_dec(v_cidx_7497_);
                            crate::leanh::lean_dec(v_cidx_7494_);
                            v___y_7500_ = v___x_7502_;
                            state = 6;
                            continue;
                        } else {
                            v___x_7503_ = lean_nat_dec_eq(v_cidx_7494_, v_cidx_7497_);
                            crate::leanh::lean_dec(v_cidx_7497_);
                            crate::leanh::lean_dec(v_cidx_7494_);
                            v___y_7500_ = v___x_7503_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 3);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7504_ = 0;
                        return v___x_7504_;
                    }
                }
                4 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 4 {
                        v_x_7505_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7505_);
                        v_i_7506_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_i_7506_);
                        v_y_7507_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc(v_y_7507_);
                        v_b_7508_ = crate::leanh::lean_ctor_get(v_x_7415_, 3);
                        crate::leanh::lean_inc(v_b_7508_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        v_x_7509_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7509_);
                        v_i_7510_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_i_7510_);
                        v_y_7511_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc(v_y_7511_);
                        v_b_7512_ = crate::leanh::lean_ctor_get(v_x_7416_, 3);
                        crate::leanh::lean_inc(v_b_7512_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7517_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7505_, v_x_7509_);
                        crate::leanh::lean_dec(v_x_7509_);
                        crate::leanh::lean_dec(v_x_7505_);
                        if v___x_7517_ == 0 {
                            crate::leanh::lean_dec(v_i_7510_);
                            crate::leanh::lean_dec(v_i_7506_);
                            v___y_7514_ = v___x_7517_;
                            state = 7;
                            continue;
                        } else {
                            v___x_7518_ = lean_nat_dec_eq(v_i_7506_, v_i_7510_);
                            crate::leanh::lean_dec(v_i_7510_);
                            crate::leanh::lean_dec(v_i_7506_);
                            v___y_7514_ = v___x_7518_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7519_ = 0;
                        return v___x_7519_;
                    }
                }
                5 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 5 {
                        v_x_7520_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7520_);
                        v_i_7521_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_i_7521_);
                        v_offset_7522_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc(v_offset_7522_);
                        v_y_7523_ = crate::leanh::lean_ctor_get(v_x_7415_, 3);
                        crate::leanh::lean_inc(v_y_7523_);
                        v_ty_7524_ = crate::leanh::lean_ctor_get(v_x_7415_, 4);
                        crate::leanh::lean_inc(v_ty_7524_);
                        v_b_7525_ = crate::leanh::lean_ctor_get(v_x_7415_, 5);
                        crate::leanh::lean_inc(v_b_7525_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 6);
                        v_x_7526_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7526_);
                        v_i_7527_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_i_7527_);
                        v_offset_7528_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc(v_offset_7528_);
                        v_y_7529_ = crate::leanh::lean_ctor_get(v_x_7416_, 3);
                        crate::leanh::lean_inc(v_y_7529_);
                        v_ty_7530_ = crate::leanh::lean_ctor_get(v_x_7416_, 4);
                        crate::leanh::lean_inc(v_ty_7530_);
                        v_b_7531_ = crate::leanh::lean_ctor_get(v_x_7416_, 5);
                        crate::leanh::lean_inc(v_b_7531_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 6);
                        v___x_7532_ = lean_nat_dec_eq(v_offset_7522_, v_offset_7528_);
                        crate::leanh::lean_dec(v_offset_7528_);
                        crate::leanh::lean_dec(v_offset_7522_);
                        v___x_7538_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7520_, v_x_7526_);
                        crate::leanh::lean_dec(v_x_7526_);
                        crate::leanh::lean_dec(v_x_7520_);
                        if v___x_7538_ == 0 {
                            crate::leanh::lean_dec(v_i_7527_);
                            crate::leanh::lean_dec(v_i_7521_);
                            v___y_7534_ = v___x_7538_;
                            state = 8;
                            continue;
                        } else {
                            v___x_7539_ = lean_nat_dec_eq(v_i_7521_, v_i_7527_);
                            crate::leanh::lean_dec(v_i_7527_);
                            crate::leanh::lean_dec(v_i_7521_);
                            v___y_7534_ = v___x_7539_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 6);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7540_ = 0;
                        return v___x_7540_;
                    }
                }
                6 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 6 {
                        v_x_7541_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7541_);
                        v_n_7542_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_n_7542_);
                        v_c_7543_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_7544_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7545_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc(v_b_7545_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 3);
                        v_x_7546_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7546_);
                        v_n_7547_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_n_7547_);
                        v_c_7548_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_7549_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7550_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc(v_b_7550_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 3);
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
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 3);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7551_ = 0;
                        return v___x_7551_;
                    }
                }
                7 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 7 {
                        v_x_7552_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7552_);
                        v_n_7553_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_n_7553_);
                        v_c_7554_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_7555_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7415_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7556_ = crate::leanh::lean_ctor_get(v_x_7415_, 2);
                        crate::leanh::lean_inc(v_b_7556_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 3);
                        v_x_7557_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7557_);
                        v_n_7558_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_n_7558_);
                        v_c_7559_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        );
                        v_persistent_7560_ = crate::leanh::lean_ctor_get_uint8(
                            v_x_7416_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        );
                        v_b_7561_ = crate::leanh::lean_ctor_get(v_x_7416_, 2);
                        crate::leanh::lean_inc(v_b_7561_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 3);
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
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 3);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7562_ = 0;
                        return v___x_7562_;
                    }
                }
                8 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 8 {
                        v_x_7563_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7563_);
                        v_b_7564_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_b_7564_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 2);
                        v_x_7565_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7565_);
                        v_b_7566_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_b_7566_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 2);
                        v___x_7567_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7563_, v_x_7565_);
                        crate::leanh::lean_dec(v_x_7565_);
                        crate::leanh::lean_dec(v_x_7563_);
                        if v___x_7567_ == 0 {
                            crate::leanh::lean_dec(v_b_7566_);
                            crate::leanh::lean_dec(v_b_7564_);
                            crate::leanh::lean_dec(v_x_7414_);
                            return v___x_7567_;
                        } else {
                            v_x_7415_ = v_b_7564_;
                            v_x_7416_ = v_b_7566_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 2);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7569_ = 0;
                        return v___x_7569_;
                    }
                }
                9 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 9 {
                        v_tid_7570_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_tid_7570_);
                        v_x_7571_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc(v_x_7571_);
                        v_cs_7572_ = crate::leanh::lean_ctor_get(v_x_7415_, 3);
                        crate::leanh::lean_inc_ref(v_cs_7572_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        v_tid_7573_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_tid_7573_);
                        v_x_7574_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc(v_x_7574_);
                        v_cs_7575_ = crate::leanh::lean_ctor_get(v_x_7416_, 3);
                        crate::leanh::lean_inc_ref(v_cs_7575_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 4);
                        v___x_7582_ = lean_name_eq(v_tid_7570_, v_tid_7573_);
                        crate::leanh::lean_dec(v_tid_7573_);
                        crate::leanh::lean_dec(v_tid_7570_);
                        if v___x_7582_ == 0 {
                            crate::leanh::lean_dec(v_x_7574_);
                            crate::leanh::lean_dec(v_x_7571_);
                            v___y_7577_ = v___x_7582_;
                            state = 9;
                            continue;
                        } else {
                            v___x_7583_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_x_7571_, v_x_7574_);
                            crate::leanh::lean_dec(v_x_7574_);
                            crate::leanh::lean_dec(v_x_7571_);
                            v___y_7577_ = v___x_7583_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 4);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7584_ = 0;
                        return v___x_7584_;
                    }
                }
                10 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 10 {
                        v_x_7585_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_x_7585_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 1);
                        v_x_7586_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_x_7586_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 1);
                        v___x_7587_ = l_Lean_IR_Arg_alphaEqv(v_x_7414_, v_x_7585_, v_x_7586_);
                        crate::leanh::lean_dec(v_x_7586_);
                        crate::leanh::lean_dec(v_x_7585_);
                        crate::leanh::lean_dec(v_x_7414_);
                        return v___x_7587_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 1);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7588_ = 0;
                        return v___x_7588_;
                    }
                }
                11 => {
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 11 {
                        v_j_7589_ = crate::leanh::lean_ctor_get(v_x_7415_, 0);
                        crate::leanh::lean_inc(v_j_7589_);
                        v_ys_7590_ = crate::leanh::lean_ctor_get(v_x_7415_, 1);
                        crate::leanh::lean_inc_ref(v_ys_7590_);
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 2);
                        v_j_7591_ = crate::leanh::lean_ctor_get(v_x_7416_, 0);
                        crate::leanh::lean_inc(v_j_7591_);
                        v_ys_7592_ = crate::leanh::lean_ctor_get(v_x_7416_, 1);
                        crate::leanh::lean_inc_ref(v_ys_7592_);
                        crate::leanh::lean_dec_ref_known(v_x_7416_, 2);
                        v___x_7593_ = lean_nat_dec_eq(v_j_7589_, v_j_7591_);
                        crate::leanh::lean_dec(v_j_7591_);
                        crate::leanh::lean_dec(v_j_7589_);
                        if v___x_7593_ == 0 {
                            crate::leanh::lean_dec_ref(v_ys_7592_);
                            crate::leanh::lean_dec_ref(v_ys_7590_);
                            crate::leanh::lean_dec(v_x_7414_);
                            return v___x_7593_;
                        } else {
                            v___x_7594_ =
                                l_Lean_IR_args_alphaEqv(v_x_7414_, v_ys_7590_, v_ys_7592_);
                            crate::leanh::lean_dec_ref(v_ys_7592_);
                            crate::leanh::lean_dec_ref(v_ys_7590_);
                            crate::leanh::lean_dec(v_x_7414_);
                            return v___x_7594_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_7415_, 2);
                        crate::leanh::lean_dec(v_x_7416_);
                        crate::leanh::lean_dec(v_x_7414_);
                        v___x_7595_ = 0;
                        return v___x_7595_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_x_7414_);
                    if crate::leanh::lean_obj_tag(v_x_7416_) == 12 {
                        v___x_7596_ = 1;
                        return v___x_7596_;
                    } else {
                        crate::leanh::lean_dec(v_x_7416_);
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
                        crate::leanh::lean_dec(v___y_7422_);
                        crate::leanh::lean_dec(v___y_7420_);
                        crate::leanh::lean_dec(v___y_7419_);
                        return v___y_7421_;
                    }
                } else {
                    if v___y_7418_ == 0 {
                        crate::leanh::lean_dec(v___y_7422_);
                        crate::leanh::lean_dec(v___y_7420_);
                        crate::leanh::lean_dec(v___y_7419_);
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
                    crate::leanh::lean_dec(v___y_7432_);
                    crate::leanh::lean_dec(v___y_7428_);
                    crate::leanh::lean_dec(v___y_7427_);
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
                            crate::leanh::lean_dec(v___y_7432_);
                            crate::leanh::lean_dec(v___y_7428_);
                            crate::leanh::lean_dec(v___y_7427_);
                            return v___y_7431_;
                        }
                    } else {
                        if v___y_7430_ == 0 {
                            crate::leanh::lean_dec(v___y_7432_);
                            crate::leanh::lean_dec(v___y_7428_);
                            crate::leanh::lean_dec(v___y_7427_);
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
                crate::leanh::lean_dec(v_x_u2082_7441_);
                crate::leanh::lean_dec(v_x_u2081_7436_);
                if v___x_7446_ == 0 {
                    crate::leanh::lean_dec(v_n_u2082_7442_);
                    crate::leanh::lean_dec(v_n_u2081_7437_);
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
                    crate::leanh::lean_dec(v_n_u2082_7442_);
                    crate::leanh::lean_dec(v_n_u2081_7437_);
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
                    crate::leanh::lean_dec(v_b_7455_);
                    crate::leanh::lean_dec(v_x_7452_);
                    crate::leanh::lean_dec(v_b_7451_);
                    crate::leanh::lean_dec(v_x_7448_);
                    crate::leanh::lean_dec(v_x_7414_);
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
                    crate::leanh::lean_dec(v_b_7485_);
                    crate::leanh::lean_dec(v_y_7484_);
                    crate::leanh::lean_dec(v_b_7481_);
                    crate::leanh::lean_dec(v_y_7480_);
                    crate::leanh::lean_dec(v_x_7414_);
                    return v___y_7487_;
                } else {
                    v___x_7488_ = l_Lean_IR_Arg_alphaEqv(v_x_7414_, v_y_7480_, v_y_7484_);
                    crate::leanh::lean_dec(v_y_7484_);
                    crate::leanh::lean_dec(v_y_7480_);
                    if v___x_7488_ == 0 {
                        crate::leanh::lean_dec(v_b_7485_);
                        crate::leanh::lean_dec(v_b_7481_);
                        crate::leanh::lean_dec(v_x_7414_);
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
                    crate::leanh::lean_dec(v_b_7498_);
                    crate::leanh::lean_dec(v_b_7495_);
                    crate::leanh::lean_dec(v_x_7414_);
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
                    crate::leanh::lean_dec(v_b_7512_);
                    crate::leanh::lean_dec(v_y_7511_);
                    crate::leanh::lean_dec(v_b_7508_);
                    crate::leanh::lean_dec(v_y_7507_);
                    crate::leanh::lean_dec(v_x_7414_);
                    return v___y_7514_;
                } else {
                    v___x_7515_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_y_7507_, v_y_7511_);
                    crate::leanh::lean_dec(v_y_7511_);
                    crate::leanh::lean_dec(v_y_7507_);
                    if v___x_7515_ == 0 {
                        crate::leanh::lean_dec(v_b_7512_);
                        crate::leanh::lean_dec(v_b_7508_);
                        crate::leanh::lean_dec(v_x_7414_);
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
                    crate::leanh::lean_dec(v_b_7531_);
                    crate::leanh::lean_dec(v_ty_7530_);
                    crate::leanh::lean_dec(v_y_7529_);
                    crate::leanh::lean_dec(v_b_7525_);
                    crate::leanh::lean_dec(v_ty_7524_);
                    crate::leanh::lean_dec(v_y_7523_);
                    crate::leanh::lean_dec(v_x_7414_);
                    return v___y_7534_;
                } else {
                    if v___x_7532_ == 0 {
                        crate::leanh::lean_dec(v_b_7531_);
                        crate::leanh::lean_dec(v_ty_7530_);
                        crate::leanh::lean_dec(v_y_7529_);
                        crate::leanh::lean_dec(v_b_7525_);
                        crate::leanh::lean_dec(v_ty_7524_);
                        crate::leanh::lean_dec(v_y_7523_);
                        crate::leanh::lean_dec(v_x_7414_);
                        return v___x_7532_;
                    } else {
                        v___x_7535_ = l_Lean_IR_VarId_alphaEqv(v_x_7414_, v_y_7523_, v_y_7529_);
                        crate::leanh::lean_dec(v_y_7529_);
                        crate::leanh::lean_dec(v_y_7523_);
                        if v___x_7535_ == 0 {
                            crate::leanh::lean_dec(v_b_7531_);
                            crate::leanh::lean_dec(v_ty_7530_);
                            crate::leanh::lean_dec(v_b_7525_);
                            crate::leanh::lean_dec(v_ty_7524_);
                            crate::leanh::lean_dec(v_x_7414_);
                            return v___x_7535_;
                        } else {
                            v___x_7536_ = l_Lean_IR_instBEqIRType_beq(v_ty_7524_, v_ty_7530_);
                            crate::leanh::lean_dec(v_ty_7530_);
                            crate::leanh::lean_dec(v_ty_7524_);
                            if v___x_7536_ == 0 {
                                crate::leanh::lean_dec(v_b_7531_);
                                crate::leanh::lean_dec(v_b_7525_);
                                crate::leanh::lean_dec(v_x_7414_);
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
                    crate::leanh::lean_dec_ref(v_cs_7575_);
                    crate::leanh::lean_dec_ref(v_cs_7572_);
                    crate::leanh::lean_dec(v_x_7414_);
                    return v___y_7577_;
                } else {
                    v___x_7578_ = lean_array_get_size(v_cs_7572_);
                    v___x_7579_ = lean_array_get_size(v_cs_7575_);
                    v___x_7580_ = lean_nat_dec_eq(v___x_7578_, v___x_7579_);
                    if v___x_7580_ == 0 {
                        crate::leanh::lean_dec_ref(v_cs_7575_);
                        crate::leanh::lean_dec_ref(v_cs_7572_);
                        crate::leanh::lean_dec(v_x_7414_);
                        return v___x_7580_;
                    } else {
                        v___x_7581_ =
                            l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
                                v_x_7414_,
                                v_cs_7572_,
                                v_cs_7575_,
                                v___x_7578_,
                            );
                        crate::leanh::lean_dec_ref(v_cs_7575_);
                        crate::leanh::lean_dec_ref(v_cs_7572_);
                        return v___x_7581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
    mut v_x_7598_: *mut crate::leanh::LeanObject,
    mut v_xs_7599_: *mut crate::leanh::LeanObject,
    mut v_ys_7600_: *mut crate::leanh::LeanObject,
    mut v_x_7601_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7603_: u8 = 0;
    let mut v_one_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7607_: u8 = 0;
    let mut v___x_7609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_7611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: u8 = 0;
    let mut v___x_7616_: u8 = 0;
    let mut v_b_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_7618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7602_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_7603_ = lean_nat_dec_eq(v_x_7601_, v_zero_7602_);
                if v_isZero_7603_ == 1 {
                    crate::leanh::lean_dec(v_x_7601_);
                    crate::leanh::lean_dec(v_x_7598_);
                    return v_isZero_7603_;
                } else {
                    v_one_7604_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_7605_ = lean_nat_sub(v_x_7601_, v_one_7604_);
                    crate::leanh::lean_dec(v_x_7601_);
                    v___x_7609_ = lean_array_fget_borrowed(v_xs_7599_, v_n_7605_);
                    v___x_7610_ = lean_array_fget_borrowed(v_ys_7600_, v_n_7605_);
                    if crate::leanh::lean_obj_tag(v___x_7609_) == 0 {
                        if crate::leanh::lean_obj_tag(v___x_7610_) == 0 {
                            v_info_7611_ = crate::leanh::lean_ctor_get(v___x_7609_, 0);
                            v_b_7612_ = crate::leanh::lean_ctor_get(v___x_7609_, 1);
                            v_info_7613_ = crate::leanh::lean_ctor_get(v___x_7610_, 0);
                            v_b_7614_ = crate::leanh::lean_ctor_get(v___x_7610_, 1);
                            v___x_7615_ = l_Lean_IR_instBEqCtorInfo_beq(v_info_7611_, v_info_7613_);
                            if v___x_7615_ == 0 {
                                v___y_7607_ = v___x_7615_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_b_7614_);
                                crate::leanh::lean_inc(v_b_7612_);
                                crate::leanh::lean_inc(v_x_7598_);
                                v___x_7616_ =
                                    l_Lean_IR_FnBody_alphaEqv(v_x_7598_, v_b_7612_, v_b_7614_);
                                v___y_7607_ = v___x_7616_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_n_7605_);
                            crate::leanh::lean_dec(v_x_7598_);
                            return v_isZero_7603_;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_7610_) == 1 {
                            v_b_7617_ = crate::leanh::lean_ctor_get(v___x_7609_, 0);
                            v_b_7618_ = crate::leanh::lean_ctor_get(v___x_7610_, 0);
                            crate::leanh::lean_inc(v_b_7618_);
                            crate::leanh::lean_inc(v_b_7617_);
                            crate::leanh::lean_inc(v_x_7598_);
                            v___x_7619_ =
                                l_Lean_IR_FnBody_alphaEqv(v_x_7598_, v_b_7617_, v_b_7618_);
                            v___y_7607_ = v___x_7619_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_n_7605_);
                            crate::leanh::lean_dec(v_x_7598_);
                            return v_isZero_7603_;
                        }
                    }
                }
            }
            1 => {
                if v___y_7607_ == 0 {
                    crate::leanh::lean_dec(v_n_7605_);
                    crate::leanh::lean_dec(v_x_7598_);
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
    mut v_x_7620_: *mut crate::leanh::LeanObject,
    mut v_xs_7621_: *mut crate::leanh::LeanObject,
    mut v_ys_7622_: *mut crate::leanh::LeanObject,
    mut v_x_7623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7624_: u8 = 0;
    let mut v_r_7625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7624_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
        v_x_7620_, v_xs_7621_, v_ys_7622_, v_x_7623_,
    );
    crate::leanh::lean_dec_ref(v_ys_7622_);
    crate::leanh::lean_dec_ref(v_xs_7621_);
    v_r_7625_ = crate::leanh::lean_box((v_res_7624_) as usize);
    return v_r_7625_;
}
pub unsafe fn l_Lean_IR_FnBody_alphaEqv___boxed(
    mut v_x_7626_: *mut crate::leanh::LeanObject,
    mut v_x_7627_: *mut crate::leanh::LeanObject,
    mut v_x_7628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7629_: u8 = 0;
    let mut v_r_7630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7629_ = l_Lean_IR_FnBody_alphaEqv(v_x_7626_, v_x_7627_, v_x_7628_);
    v_r_7630_ = crate::leanh::lean_box((v_res_7629_) as usize);
    return v_r_7630_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(
    mut v_x_7631_: *mut crate::leanh::LeanObject,
    mut v_xs_7632_: *mut crate::leanh::LeanObject,
    mut v_ys_7633_: *mut crate::leanh::LeanObject,
    mut v_hsz_7634_: *mut crate::leanh::LeanObject,
    mut v_x_7635_: *mut crate::leanh::LeanObject,
    mut v_x_7636_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7637_: u8 = 0;
    v___x_7637_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___redArg(
        v_x_7631_, v_xs_7632_, v_ys_7633_, v_x_7635_,
    );
    return v___x_7637_;
}
pub unsafe fn l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0___boxed(
    mut v_x_7638_: *mut crate::leanh::LeanObject,
    mut v_xs_7639_: *mut crate::leanh::LeanObject,
    mut v_ys_7640_: *mut crate::leanh::LeanObject,
    mut v_hsz_7641_: *mut crate::leanh::LeanObject,
    mut v_x_7642_: *mut crate::leanh::LeanObject,
    mut v_x_7643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7644_: u8 = 0;
    let mut v_r_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7644_ = l_Array_isEqvAux___at___00Lean_IR_FnBody_alphaEqv_spec__0(
        v_x_7638_,
        v_xs_7639_,
        v_ys_7640_,
        v_hsz_7641_,
        v_x_7642_,
        v_x_7643_,
    );
    crate::leanh::lean_dec_ref(v_ys_7640_);
    crate::leanh::lean_dec_ref(v_xs_7639_);
    v_r_7645_ = crate::leanh::lean_box((v_res_7644_) as usize);
    return v_r_7645_;
}
pub unsafe fn l_Lean_IR_FnBody_beq(
    mut v_b_u2081_7646_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_7647_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: u8 = 0;
    v___x_7648_ = crate::leanh::lean_box(1);
    v___x_7649_ = l_Lean_IR_FnBody_alphaEqv(v___x_7648_, v_b_u2081_7646_, v_b_u2082_7647_);
    return v___x_7649_;
}
pub unsafe fn l_Lean_IR_FnBody_beq___boxed(
    mut v_b_u2081_7650_: *mut crate::leanh::LeanObject,
    mut v_b_u2082_7651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7652_: u8 = 0;
    let mut v_r_7653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7652_ = l_Lean_IR_FnBody_beq(v_b_u2081_7650_, v_b_u2082_7651_);
    v_r_7653_ = crate::leanh::lean_box((v_res_7652_) as usize);
    return v_r_7653_;
}
pub unsafe fn l_Lean_IR_mkIf(
    mut v_x_7674_: *mut crate::leanh::LeanObject,
    mut v_t_7675_: *mut crate::leanh::LeanObject,
    mut v_e_7676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7677_ = l_Lean_IR_mkIf___closed__1;
    v___x_7678_ = crate::leanh::lean_box(1);
    v___x_7679_ = l_Lean_IR_mkIf___closed__4;
    v___x_7680_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7680_, 0, v___x_7679_);
    crate::leanh::lean_ctor_set(v___x_7680_, 1, v_e_7676_);
    v___x_7681_ = l_Lean_IR_mkIf___closed__7;
    v___x_7682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7682_, 0, v___x_7681_);
    crate::leanh::lean_ctor_set(v___x_7682_, 1, v_t_7675_);
    v___x_7683_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_7684_ = lean_mk_empty_array_with_capacity(v___x_7683_);
    v___x_7685_ = lean_array_push(v___x_7684_, v___x_7680_);
    v___x_7686_ = lean_array_push(v___x_7685_, v___x_7682_);
    v___x_7687_ = crate::leanh::lean_alloc_ctor(9, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7687_, 0, v___x_7677_);
    crate::leanh::lean_ctor_set(v___x_7687_, 1, v_x_7674_);
    crate::leanh::lean_ctor_set(v___x_7687_, 2, v___x_7678_);
    crate::leanh::lean_ctor_set(v___x_7687_, 3, v___x_7686_);
    return v___x_7687_;
}
pub unsafe fn l_Lean_IR_getUnboxOpName(
    mut v_t_7694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_7694_) {
        5 => {
            let mut v___x_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7695_ = l_Lean_IR_getUnboxOpName___closed__0;
            return v___x_7695_;
        }
        3 => {
            let mut v___x_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7696_ = l_Lean_IR_getUnboxOpName___closed__1;
            return v___x_7696_;
        }
        4 => {
            let mut v___x_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7697_ = l_Lean_IR_getUnboxOpName___closed__2;
            return v___x_7697_;
        }
        0 => {
            let mut v___x_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7698_ = l_Lean_IR_getUnboxOpName___closed__3;
            return v___x_7698_;
        }
        9 => {
            let mut v___x_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7699_ = l_Lean_IR_getUnboxOpName___closed__4;
            return v___x_7699_;
        }
        _ => {
            let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_7700_ = l_Lean_IR_getUnboxOpName___closed__5;
            return v___x_7700_;
        }
    }
}
pub unsafe fn l_Lean_IR_getUnboxOpName___boxed(
    mut v_t_7701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7702_ = l_Lean_IR_getUnboxOpName(v_t_7701_);
    crate::leanh::lean_dec(v_t_7701_);
    return v_res_7702_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_IR_instInhabitedVarId_default = _init_l_Lean_IR_instInhabitedVarId_default();
    crate::leanh::lean_mark_persistent(l_Lean_IR_instInhabitedVarId_default);
    l_Lean_IR_instInhabitedVarId = _init_l_Lean_IR_instInhabitedVarId();
    crate::leanh::lean_mark_persistent(l_Lean_IR_instInhabitedVarId);
    l_Lean_IR_instInhabitedJoinPointId_default = _init_l_Lean_IR_instInhabitedJoinPointId_default();
    crate::leanh::lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId_default);
    l_Lean_IR_instInhabitedJoinPointId = _init_l_Lean_IR_instInhabitedJoinPointId();
    crate::leanh::lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId);
    l_Lean_IR_instInhabitedIRType_default = _init_l_Lean_IR_instInhabitedIRType_default();
    crate::leanh::lean_mark_persistent(l_Lean_IR_instInhabitedIRType_default);
    l_Lean_IR_instInhabitedIRType = _init_l_Lean_IR_instInhabitedIRType();
    crate::leanh::lean_mark_persistent(l_Lean_IR_instInhabitedIRType);
    l_Lean_IR_FnBody_nil = _init_l_Lean_IR_FnBody_nil();
    crate::leanh::lean_mark_persistent(l_Lean_IR_FnBody_nil);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_ExternAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_Basic(builtin);
}
