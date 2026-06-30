// Lean compiler output
// Module: Std.Sat.AIG.Basic
// Imports: Std.Data.HashSet Init.Data.Vector.Basic Init.Data.Hashable Init.Data.String.Defs Init.Data.ToString.Macro Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_mk_array, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_land, lean_nat_lor, lean_nat_lxor, lean_nat_mul,
    lean_nat_shiftr, lean_nat_to_int, lean_string_append, lean_string_length, lean_uint64_mix_hash,
    lean_uint64_of_nat, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::UInt::BasicAux::l_UInt64_ofNat___boxed;
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node5, l_Lean_Syntax_node7,
    l_Lean_addMacroScope, l_String_toRawSubstring_x27,
    l_instBEqOfDecidableEq___redArg___lam__0___boxed, l_instDecidableEqFin___boxed,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::l_Std_DHashMap_Internal_AssocList_foldlM___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insert___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
use crate::r#gen::Std::Data::HashSet::{
    initialize_Std_Data_HashSet, runtime_initialize_Std_Data_HashSet,
};
pub static l_Std_Sat_AIG_instHashableFanin___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Sat_AIG_instHashableFanin_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_instHashableFanin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instHashableFanin___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Sat_AIG_instHashableFanin: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instHashableFanin___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1_value:
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
    m_data: [118, 97, 108, 0],
};
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprFanin___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Sat_AIG_instReprFanin_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_instReprFanin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Sat_AIG_instReprFanin: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprFanin___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Sat_AIG_instInhabitedFanin_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Sat_AIG_instInhabitedFanin: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        83, 116, 100, 46, 83, 97, 116, 46, 65, 73, 71, 46, 68, 101, 99, 108, 46, 102, 97, 108, 115,
        101, 0,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        83, 116, 100, 46, 83, 97, 116, 46, 65, 73, 71, 46, 68, 101, 99, 108, 46, 97, 116, 111, 109,
        0,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        83, 116, 100, 46, 83, 97, 116, 46, 65, 73, 71, 46, 68, 101, 99, 108, 46, 103, 97, 116, 101,
        0,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG_Cache_empty___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_Cache_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Sat_AIG_Cache_empty___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_Cache_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Sat_AIG_empty___closed__0_value: leanh::LeanArrayObject<1> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 1,
        m_capacity: 1,
        m_data: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Sat_AIG_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_empty___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG_empty___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_empty___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0_value: leanh::LeanStringObject<
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
    m_data: [32, 91, 99, 111, 108, 111, 114, 61, 98, 108, 117, 101, 93, 0],
};
static mut l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1_value: leanh::LeanStringObject<
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
    m_data: [32, 91, 99, 111, 108, 111, 114, 61, 114, 101, 100, 93, 0],
};
static mut l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_ofNat___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 45, 62, 32, 0],
};
static mut l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [59, 32, 0],
};
static mut l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [59, 0],
};
static mut l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [32, 91, 108, 97, 98, 101, 108, 61, 34, 0],
};
static mut l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        34, 44, 32, 115, 104, 97, 112, 101, 61, 98, 111, 120, 93, 59, 0,
    ],
};
static mut l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        34, 44, 32, 115, 104, 97, 112, 101, 61, 100, 111, 117, 98, 108, 101, 99, 105, 114, 99, 108,
        101, 93, 59, 0,
    ],
};
static mut l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 21,
    m_data: [
        32, 226, 136, 167, 34, 44, 115, 104, 97, 112, 101, 61, 116, 114, 97, 112, 101, 122, 105,
        117, 109, 93, 59, 0,
    ],
};
static mut l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__0_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__3_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [68, 105, 103, 114, 97, 112, 104, 32, 65, 73, 71, 32, 123, 0],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__4_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [125, 0],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__12_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_toGraphviz___redArg___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_toGraphviz___redArg___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_toGraphviz___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value:
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
    m_data: [83, 116, 100, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value:
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
    m_data: [83, 97, 116, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value:
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
    m_data: [65, 73, 71, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 9,
    m_data: [
        116, 101, 114, 109, 226, 159, 166, 95, 44, 95, 226, 159, 167, 0,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value)
            as *mut leanh::LeanObject,
        5627605678714606251 as *mut leanh::LeanObject,
    ],
};
static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value)
            as *mut leanh::LeanObject,
        10534633952002991263 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__3_value)
            as *mut leanh::LeanObject,
        8167817868804045124 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__5_value)
            as *mut leanh::LeanObject,
        12571085391447129896 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 166, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__9_value)
            as *mut leanh::LeanObject,
        8609355255726335675 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__10_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__12_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 159, 167, 0],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__19_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Sat_AIG_term_u27e6___x2c___u27e7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 11,
    m_data: [
        116, 101, 114, 109, 226, 159, 166, 95, 44, 95, 44, 95, 226, 159, 167, 0,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value)
            as *mut leanh::LeanObject,
        5627605678714606251 as *mut leanh::LeanObject,
    ],
};
static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value)
            as *mut leanh::LeanObject,
        10534633952002991263 as *mut leanh::LeanObject,
    ],
};
pub static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__0_value)
            as *mut leanh::LeanObject,
        10887712157934851851 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__16_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1_value)
            as *mut leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value) as *mut leanh::LeanObject;
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__3_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 110, 111, 116, 101, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value) as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value) as *mut leanh::LeanObject,11776781845681970536 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7_value) as *mut leanh::LeanObject;
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value) as *mut leanh::LeanObject,5627605678714606251 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value) as *mut leanh::LeanObject,10534633952002991263 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5_value) as *mut leanh::LeanObject,16783667355711570012 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__11_value) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__13_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject;
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__5_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6_value) as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value) as *mut leanh::LeanObject,5627605678714606251 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value) as *mut leanh::LeanObject,10534633952002991263 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__8_value) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [69, 110, 116, 114, 121, 112, 111, 105, 110, 116, 46, 109, 107, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11_value) as *mut leanh::LeanObject;
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [69, 110, 116, 114, 121, 112, 111, 105, 110, 116, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value) as *mut leanh::LeanObject;
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value) as *mut leanh::LeanObject,3010196996240522784 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value) as *mut leanh::LeanObject,9758975459823336856 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15_value) as *mut leanh::LeanObject;
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__1_value) as *mut leanh::LeanObject,5627605678714606251 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__2_value) as *mut leanh::LeanObject,10534633952002991263 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__13_value) as *mut leanh::LeanObject,6502570156926630868 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__14_value) as *mut leanh::LeanObject,15650536001181337276 as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__16_value) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__18_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__17_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__19_value) as *mut leanh::LeanObject] };
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__0_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG_unexpandDenote___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__0_value)
                as *mut leanh::LeanObject,
            2026475204632980274 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Sat_AIG_unexpandDenote___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__3_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__3_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG_unexpandDenote___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__3_value)
                as *mut leanh::LeanObject,
            5018042693327868416 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__5_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__5_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG_unexpandDenote___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__6_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__5_value)
                as *mut leanh::LeanObject,
            6117808163008040242 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__7_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__7_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG_unexpandDenote___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__8_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__7_value)
                as *mut leanh::LeanObject,
            14295752356045161913 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__9_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [97, 105, 103, 0],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__9_value)
                as *mut leanh::LeanObject,
            8473776652682600307 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__11_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
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
            115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__11_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG_unexpandDenote___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__12_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__11_value)
                as *mut leanh::LeanObject,
            7440505896048223825 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__13_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [115, 116, 97, 114, 116, 0],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__13_value)
                as *mut leanh::LeanObject,
            12748178501718933929 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__15_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 110, 118, 0],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__15_value)
                as *mut leanh::LeanObject,
            6206193998513246702 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__17_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__17_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG_unexpandDenote___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__18_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__17_value)
                as *mut leanh::LeanObject,
            11580369617518985485 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__19_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__19_value)
        as *mut leanh::LeanObject;
static l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Sat_AIG_unexpandDenote___closed__20_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__20_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__19_value)
                as *mut leanh::LeanObject,
            13429426995999683896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__21_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 159, 168, 0],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Sat_AIG_unexpandDenote___closed__22_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 159, 169, 0],
    };
static mut l_Std_Sat_AIG_unexpandDenote___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_unexpandDenote___closed__22_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Sat_AIG_instHashableFanin_hash(
    mut v_x_2190_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_2191_: u64 = 0;
    let mut v___x_2192_: u64 = 0;
    let mut v___x_2193_: u64 = 0;
    v___x_2191_ = 0u64;
    v___x_2192_ = lean_uint64_of_nat(v_x_2190_);
    v___x_2193_ = lean_uint64_mix_hash(v___x_2191_, v___x_2192_);
    return v___x_2193_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableFanin_hash___boxed(
    mut v_x_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2195_: u64 = 0;
    let mut v_r_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Sat_AIG_instHashableFanin_hash(v_x_2194_);
    leanh::lean_dec(v_x_2194_);
    v_r_2196_ = leanh::lean_box_uint64(v_res_2195_);
    return v_r_2196_;
}
pub unsafe fn l_Nat_cast___at___00Std_Sat_AIG_instReprFanin_repr_spec__0(
    mut v_a_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = lean_nat_to_int(v_a_2199_);
    return v___x_2200_;
}
pub unsafe fn _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = leanh::lean_unsigned_to_nat(7);
    v___x_2215_ = lean_nat_to_int(v___x_2214_);
    return v___x_2215_;
}
pub unsafe fn _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__0;
    v___x_2218_ = lean_string_length(v___x_2217_);
    return v___x_2218_;
}
pub unsafe fn _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2219_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9_once),
        _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__9,
    );
    v___x_2220_ = lean_nat_to_int(v___x_2219_);
    return v___x_2220_;
}
pub unsafe fn l_Std_Sat_AIG_instReprFanin_repr___redArg(
    mut v_x_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2226_ = l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__6;
    v___x_2227_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7_once),
        _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__7,
    );
    v___x_2228_ = l_Nat_reprFast(v_x_2225_);
    v___x_2229_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2229_, 0, v___x_2228_);
    v___x_2230_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2230_, 0, v___x_2227_);
    leanh::lean_ctor_set(v___x_2230_, 1, v___x_2229_);
    v___x_2231_ = 0;
    v___x_2232_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2232_, 0, v___x_2230_);
    leanh::lean_ctor_set_uint8(
        v___x_2232_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2231_,
    );
    v___x_2233_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2233_, 0, v___x_2226_);
    leanh::lean_ctor_set(v___x_2233_, 1, v___x_2232_);
    v___x_2234_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10_once),
        _init_l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__10,
    );
    v___x_2235_ = l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__11;
    v___x_2236_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
    leanh::lean_ctor_set(v___x_2236_, 1, v___x_2233_);
    v___x_2237_ = l_Std_Sat_AIG_instReprFanin_repr___redArg___closed__12;
    v___x_2238_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2238_, 0, v___x_2236_);
    leanh::lean_ctor_set(v___x_2238_, 1, v___x_2237_);
    v___x_2239_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2239_, 0, v___x_2234_);
    leanh::lean_ctor_set(v___x_2239_, 1, v___x_2238_);
    v___x_2240_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2240_, 0, v___x_2239_);
    leanh::lean_ctor_set_uint8(
        v___x_2240_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2231_,
    );
    return v___x_2240_;
}
pub unsafe fn l_Std_Sat_AIG_instReprFanin_repr(
    mut v_x_2241_: *mut leanh::LeanObject,
    mut v_prec_2242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_x_2241_);
    return v___x_2243_;
}
pub unsafe fn l_Std_Sat_AIG_instReprFanin_repr___boxed(
    mut v_x_2244_: *mut leanh::LeanObject,
    mut v_prec_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Std_Sat_AIG_instReprFanin_repr(v_x_2244_, v_prec_2245_);
    leanh::lean_dec(v_prec_2245_);
    return v_res_2246_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqFanin_decEq(
    mut v_x_2249_: *mut leanh::LeanObject,
    mut v_x_2250_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2251_: u8 = 0;
    v___x_2251_ = lean_nat_dec_eq(v_x_2249_, v_x_2250_);
    return v___x_2251_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqFanin_decEq___boxed(
    mut v_x_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2254_: u8 = 0;
    let mut v_r_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l_Std_Sat_AIG_instDecidableEqFanin_decEq(v_x_2252_, v_x_2253_);
    leanh::lean_dec(v_x_2253_);
    leanh::lean_dec(v_x_2252_);
    v_r_2255_ = leanh::lean_box((v_res_2254_) as usize);
    return v_r_2255_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqFanin(
    mut v_x_2256_: *mut leanh::LeanObject,
    mut v_x_2257_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2258_: u8 = 0;
    v___x_2258_ = lean_nat_dec_eq(v_x_2256_, v_x_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqFanin___boxed(
    mut v_x_2259_: *mut leanh::LeanObject,
    mut v_x_2260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2261_: u8 = 0;
    let mut v_r_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Std_Sat_AIG_instDecidableEqFanin(v_x_2259_, v_x_2260_);
    leanh::lean_dec(v_x_2260_);
    leanh::lean_dec(v_x_2259_);
    v_r_2262_ = leanh::lean_box((v_res_2261_) as usize);
    return v_r_2262_;
}
pub unsafe fn _init_l_Std_Sat_AIG_instInhabitedFanin_default() -> *mut leanh::LeanObject {
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = leanh::lean_unsigned_to_nat(0);
    return v___x_2263_;
}
pub unsafe fn _init_l_Std_Sat_AIG_instInhabitedFanin() -> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = leanh::lean_unsigned_to_nat(0);
    return v___x_2264_;
}
pub unsafe fn l_Std_Sat_AIG_Fanin_mk(
    mut v_gate_2265_: *mut leanh::LeanObject,
    mut v_invert_2266_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = leanh::lean_unsigned_to_nat(2);
    v___x_2268_ = lean_nat_mul(v_gate_2265_, v___x_2267_);
    v___x_2269_ = l_Bool_toNat(v_invert_2266_);
    v___x_2270_ = lean_nat_lor(v___x_2268_, v___x_2269_);
    leanh::lean_dec(v___x_2269_);
    leanh::lean_dec(v___x_2268_);
    return v___x_2270_;
}
pub unsafe fn l_Std_Sat_AIG_Fanin_mk___boxed(
    mut v_gate_2271_: *mut leanh::LeanObject,
    mut v_invert_2272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_invert_boxed_2273_: u8 = 0;
    let mut v_res_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_invert_boxed_2273_ = (leanh::lean_unbox(v_invert_2272_) as u8);
    v_res_2274_ = l_Std_Sat_AIG_Fanin_mk(v_gate_2271_, v_invert_boxed_2273_);
    leanh::lean_dec(v_gate_2271_);
    return v_res_2274_;
}
pub unsafe fn l_Std_Sat_AIG_Fanin_gate(
    mut v_f_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = leanh::lean_unsigned_to_nat(1);
    v___x_2277_ = lean_nat_shiftr(v_f_2275_, v___x_2276_);
    return v___x_2277_;
}
pub unsafe fn l_Std_Sat_AIG_Fanin_gate___boxed(
    mut v_f_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2279_ = l_Std_Sat_AIG_Fanin_gate(v_f_2278_);
    leanh::lean_dec(v_f_2278_);
    return v_res_2279_;
}
pub unsafe fn l_Std_Sat_AIG_Fanin_invert(mut v_f_2280_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    v___x_2281_ = leanh::lean_unsigned_to_nat(1);
    v___x_2282_ = lean_nat_land(v___x_2281_, v_f_2280_);
    v___x_2283_ = leanh::lean_unsigned_to_nat(0);
    v___x_2284_ = lean_nat_dec_eq(v___x_2282_, v___x_2283_);
    leanh::lean_dec(v___x_2282_);
    if v___x_2284_ == 0 {
        let mut v___x_2285_: u8 = 0;
        v___x_2285_ = 1;
        return v___x_2285_;
    } else {
        let mut v___x_2286_: u8 = 0;
        v___x_2286_ = 0;
        return v___x_2286_;
    }
}
pub unsafe fn l_Std_Sat_AIG_Fanin_invert___boxed(
    mut v_f_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2288_: u8 = 0;
    let mut v_r_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Std_Sat_AIG_Fanin_invert(v_f_2287_);
    leanh::lean_dec(v_f_2287_);
    v_r_2289_ = leanh::lean_box((v_res_2288_) as usize);
    return v_r_2289_;
}
pub unsafe fn l_Std_Sat_AIG_Fanin_flip(
    mut v_f_2290_: *mut leanh::LeanObject,
    mut v_val_2291_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ = l_Bool_toNat(v_val_2291_);
    v___x_2293_ = lean_nat_lxor(v_f_2290_, v___x_2292_);
    leanh::lean_dec(v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn l_Std_Sat_AIG_Fanin_flip___boxed(
    mut v_f_2294_: *mut leanh::LeanObject,
    mut v_val_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_2296_: u8 = 0;
    let mut v_res_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_2296_ = (leanh::lean_unbox(v_val_2295_) as u8);
    v_res_2297_ = l_Std_Sat_AIG_Fanin_flip(v_f_2294_, v_val_boxed_2296_);
    leanh::lean_dec(v_f_2294_);
    return v_res_2297_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_ctorIdx___redArg(
    mut v_x_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2298_) {
        0 => {
            let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2299_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2299_;
        }
        1 => {
            let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2300_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2300_;
        }
        _ => {
            let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2301_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2301_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Decl_ctorIdx___redArg___boxed(
    mut v_x_2302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2303_ = l_Std_Sat_AIG_Decl_ctorIdx___redArg(v_x_2302_);
    leanh::lean_dec(v_x_2302_);
    return v_res_2303_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_ctorIdx(
    mut v_00_u03b1_2304_: *mut leanh::LeanObject,
    mut v_x_2305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = l_Std_Sat_AIG_Decl_ctorIdx___redArg(v_x_2305_);
    return v___x_2306_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_ctorIdx___boxed(
    mut v_00_u03b1_2307_: *mut leanh::LeanObject,
    mut v_x_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_Std_Sat_AIG_Decl_ctorIdx(v_00_u03b1_2307_, v_x_2308_);
    leanh::lean_dec(v_x_2308_);
    return v_res_2309_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_ctorElim___redArg(
    mut v_t_2310_: *mut leanh::LeanObject,
    mut v_k_2311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2310_) {
        0 => {
            return v_k_2311_;
        }
        1 => {
            let mut v_idx_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_idx_2312_ = leanh::lean_ctor_get(v_t_2310_, 0);
            leanh::lean_inc(v_idx_2312_);
            leanh::lean_dec_ref_known(v_t_2310_, 1);
            v___x_2313_ = leanh::lean_apply_1(v_k_2311_, v_idx_2312_);
            return v___x_2313_;
        }
        _ => {
            let mut v_l_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_l_2314_ = leanh::lean_ctor_get(v_t_2310_, 0);
            leanh::lean_inc(v_l_2314_);
            v_r_2315_ = leanh::lean_ctor_get(v_t_2310_, 1);
            leanh::lean_inc(v_r_2315_);
            leanh::lean_dec_ref_known(v_t_2310_, 2);
            v___x_2316_ = leanh::lean_apply_2(v_k_2311_, v_l_2314_, v_r_2315_);
            return v___x_2316_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Decl_ctorElim(
    mut v_00_u03b1_2317_: *mut leanh::LeanObject,
    mut v_motive_2318_: *mut leanh::LeanObject,
    mut v_ctorIdx_2319_: *mut leanh::LeanObject,
    mut v_t_2320_: *mut leanh::LeanObject,
    mut v_h_2321_: *mut leanh::LeanObject,
    mut v_k_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2323_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_2320_, v_k_2322_);
    return v___x_2323_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_ctorElim___boxed(
    mut v_00_u03b1_2324_: *mut leanh::LeanObject,
    mut v_motive_2325_: *mut leanh::LeanObject,
    mut v_ctorIdx_2326_: *mut leanh::LeanObject,
    mut v_t_2327_: *mut leanh::LeanObject,
    mut v_h_2328_: *mut leanh::LeanObject,
    mut v_k_2329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2330_ = l_Std_Sat_AIG_Decl_ctorElim(
        v_00_u03b1_2324_,
        v_motive_2325_,
        v_ctorIdx_2326_,
        v_t_2327_,
        v_h_2328_,
        v_k_2329_,
    );
    leanh::lean_dec(v_ctorIdx_2326_);
    return v_res_2330_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_false_elim___redArg(
    mut v_t_2331_: *mut leanh::LeanObject,
    mut v_false_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_2331_, v_false_2332_);
    return v___x_2333_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_false_elim(
    mut v_00_u03b1_2334_: *mut leanh::LeanObject,
    mut v_motive_2335_: *mut leanh::LeanObject,
    mut v_t_2336_: *mut leanh::LeanObject,
    mut v_h_2337_: *mut leanh::LeanObject,
    mut v_false_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2339_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_2336_, v_false_2338_);
    return v___x_2339_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_atom_elim___redArg(
    mut v_t_2340_: *mut leanh::LeanObject,
    mut v_atom_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_2340_, v_atom_2341_);
    return v___x_2342_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_atom_elim(
    mut v_00_u03b1_2343_: *mut leanh::LeanObject,
    mut v_motive_2344_: *mut leanh::LeanObject,
    mut v_t_2345_: *mut leanh::LeanObject,
    mut v_h_2346_: *mut leanh::LeanObject,
    mut v_atom_2347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_2345_, v_atom_2347_);
    return v___x_2348_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_gate_elim___redArg(
    mut v_t_2349_: *mut leanh::LeanObject,
    mut v_gate_2350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2351_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_2349_, v_gate_2350_);
    return v___x_2351_;
}
pub unsafe fn l_Std_Sat_AIG_Decl_gate_elim(
    mut v_00_u03b1_2352_: *mut leanh::LeanObject,
    mut v_motive_2353_: *mut leanh::LeanObject,
    mut v_t_2354_: *mut leanh::LeanObject,
    mut v_h_2355_: *mut leanh::LeanObject,
    mut v_gate_2356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2357_ = l_Std_Sat_AIG_Decl_ctorElim___redArg(v_t_2354_, v_gate_2356_);
    return v___x_2357_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___redArg(
    mut v_inst_2358_: *mut leanh::LeanObject,
    mut v_x_2359_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_x_2359_) {
        0 => {
            let mut v___x_2360_: u64 = 0;
            leanh::lean_dec_ref(v_inst_2358_);
            v___x_2360_ = 0u64;
            return v___x_2360_;
        }
        1 => {
            let mut v_idx_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2362_: u64 = 0;
            let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2364_: u64 = 0;
            let mut v___x_2365_: u64 = 0;
            v_idx_2361_ = leanh::lean_ctor_get(v_x_2359_, 0);
            leanh::lean_inc(v_idx_2361_);
            leanh::lean_dec_ref_known(v_x_2359_, 1);
            v___x_2362_ = 1u64;
            v___x_2363_ = leanh::lean_apply_1(v_inst_2358_, v_idx_2361_);
            v___x_2364_ = leanh::lean_unbox_uint64(v___x_2363_);
            leanh::lean_dec_ref(v___x_2363_);
            v___x_2365_ = lean_uint64_mix_hash(v___x_2362_, v___x_2364_);
            return v___x_2365_;
        }
        _ => {
            let mut v_l_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2368_: u64 = 0;
            let mut v___x_2369_: u64 = 0;
            let mut v___x_2370_: u64 = 0;
            let mut v___x_2371_: u64 = 0;
            let mut v___x_2372_: u64 = 0;
            leanh::lean_dec_ref(v_inst_2358_);
            v_l_2366_ = leanh::lean_ctor_get(v_x_2359_, 0);
            leanh::lean_inc(v_l_2366_);
            v_r_2367_ = leanh::lean_ctor_get(v_x_2359_, 1);
            leanh::lean_inc(v_r_2367_);
            leanh::lean_dec_ref_known(v_x_2359_, 2);
            v___x_2368_ = 2u64;
            v___x_2369_ = l_Std_Sat_AIG_instHashableFanin_hash(v_l_2366_);
            leanh::lean_dec(v_l_2366_);
            v___x_2370_ = lean_uint64_mix_hash(v___x_2368_, v___x_2369_);
            v___x_2371_ = l_Std_Sat_AIG_instHashableFanin_hash(v_r_2367_);
            leanh::lean_dec(v_r_2367_);
            v___x_2372_ = lean_uint64_mix_hash(v___x_2370_, v___x_2371_);
            return v___x_2372_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___redArg___boxed(
    mut v_inst_2373_: *mut leanh::LeanObject,
    mut v_x_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2375_: u64 = 0;
    let mut v_r_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2375_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_2373_, v_x_2374_);
    v_r_2376_ = leanh::lean_box_uint64(v_res_2375_);
    return v_r_2376_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash(
    mut v_00_u03b1_2377_: *mut leanh::LeanObject,
    mut v_inst_2378_: *mut leanh::LeanObject,
    mut v_x_2379_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_2380_: u64 = 0;
    v___x_2380_ = l_Std_Sat_AIG_instHashableDecl_hash___redArg(v_inst_2378_, v_x_2379_);
    return v___x_2380_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl_hash___boxed(
    mut v_00_u03b1_2381_: *mut leanh::LeanObject,
    mut v_inst_2382_: *mut leanh::LeanObject,
    mut v_x_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2384_: u64 = 0;
    let mut v_r_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2384_ = l_Std_Sat_AIG_instHashableDecl_hash(v_00_u03b1_2381_, v_inst_2382_, v_x_2383_);
    v_r_2385_ = leanh::lean_box_uint64(v_res_2384_);
    return v_r_2385_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl___redArg(
    mut v_inst_2386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2387_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_2387_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2387_, 1, v_inst_2386_);
    return v___x_2387_;
}
pub unsafe fn l_Std_Sat_AIG_instHashableDecl(
    mut v_00_u03b1_2388_: *mut leanh::LeanObject,
    mut v_inst_2389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2390_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_2390_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2390_, 1, v_inst_2389_);
    return v___x_2390_;
}
pub unsafe fn _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = leanh::lean_unsigned_to_nat(2);
    v___x_2395_ = lean_nat_to_int(v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2396_ = leanh::lean_unsigned_to_nat(1);
    v___x_2397_ = lean_nat_to_int(v___x_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_Sat_AIG_instReprDecl_repr___redArg(
    mut v_inst_2410_: *mut leanh::LeanObject,
    mut v_x_2411_: *mut leanh::LeanObject,
    mut v_prec_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: u8 = 0;
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___y_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2411_) {
                0 => {
                    leanh::lean_dec_ref(v_inst_2410_);
                    v___x_2420_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2421_ = lean_nat_dec_le(v___x_2420_, v_prec_2412_);
                    if v___x_2421_ == 0 {
                        v___x_2422_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once
                            ),
                            _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2,
                        );
                        v___y_2414_ = v___x_2422_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2423_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once
                            ),
                            _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3,
                        );
                        v___y_2414_ = v___x_2423_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_idx_2424_ = leanh::lean_ctor_get(v_x_2411_, 0);
                    leanh::lean_inc(v_idx_2424_);
                    leanh::lean_dec_ref_known(v_x_2411_, 1);
                    v___x_2435_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2436_ = lean_nat_dec_le(v___x_2435_, v_prec_2412_);
                    if v___x_2436_ == 0 {
                        v___x_2437_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once
                            ),
                            _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2,
                        );
                        v___y_2426_ = v___x_2437_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2438_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once
                            ),
                            _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3,
                        );
                        v___y_2426_ = v___x_2438_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_inst_2410_);
                    v_l_2439_ = leanh::lean_ctor_get(v_x_2411_, 0);
                    v_r_2440_ = leanh::lean_ctor_get(v_x_2411_, 1);
                    v_isSharedCheck_2463_ = (!leanh::lean_is_exclusive(v_x_2411_)) as u8;
                    if v_isSharedCheck_2463_ == 0 {
                        v___x_2442_ = v_x_2411_;
                        v_isShared_2443_ = v_isSharedCheck_2463_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_2440_);
                        leanh::lean_inc(v_l_2439_);
                        leanh::lean_dec(v_x_2411_);
                        v___x_2442_ = leanh::lean_box(0);
                        v_isShared_2443_ = v_isSharedCheck_2463_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2415_ = l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__1;
                leanh::lean_inc(v___y_2414_);
                v___x_2416_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2416_, 0, v___y_2414_);
                leanh::lean_ctor_set(v___x_2416_, 1, v___x_2415_);
                v___x_2417_ = 0;
                v___x_2418_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2418_, 0, v___x_2416_);
                leanh::lean_ctor_set_uint8(
                    v___x_2418_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2417_,
                );
                v___x_2419_ = l_Repr_addAppParen(v___x_2418_, v_prec_2412_);
                return v___x_2419_;
            }
            2 => {
                v___x_2427_ = l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__6;
                v___x_2428_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2429_ = leanh::lean_apply_2(v_inst_2410_, v_idx_2424_, v___x_2428_);
                v___x_2430_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2430_, 0, v___x_2427_);
                leanh::lean_ctor_set(v___x_2430_, 1, v___x_2429_);
                leanh::lean_inc(v___y_2426_);
                v___x_2431_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2431_, 0, v___y_2426_);
                leanh::lean_ctor_set(v___x_2431_, 1, v___x_2430_);
                v___x_2432_ = 0;
                v___x_2433_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2433_, 0, v___x_2431_);
                leanh::lean_ctor_set_uint8(
                    v___x_2433_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2432_,
                );
                v___x_2434_ = l_Repr_addAppParen(v___x_2433_, v_prec_2412_);
                return v___x_2434_;
            }
            3 => {
                v___x_2459_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2460_ = lean_nat_dec_le(v___x_2459_, v_prec_2412_);
                if v___x_2460_ == 0 {
                    v___x_2461_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2_once
                        ),
                        _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__2,
                    );
                    v___y_2445_ = v___x_2461_;
                    state = 4;
                    continue;
                } else {
                    v___x_2462_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3_once
                        ),
                        _init_l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__3,
                    );
                    v___y_2445_ = v___x_2462_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2446_ = leanh::lean_box(1);
                v___x_2447_ = l_Std_Sat_AIG_instReprDecl_repr___redArg___closed__9;
                v___x_2448_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_l_2439_);
                if v_isShared_2443_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2442_, 5);
                    leanh::lean_ctor_set(v___x_2442_, 1, v___x_2448_);
                    leanh::lean_ctor_set(v___x_2442_, 0, v___x_2447_);
                    v___x_2450_ = v___x_2442_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 1, v___x_2448_);
                    v___x_2450_ = v_reuseFailAlloc_2458_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2451_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                leanh::lean_ctor_set(v___x_2451_, 1, v___x_2446_);
                v___x_2452_ = l_Std_Sat_AIG_instReprFanin_repr___redArg(v_r_2440_);
                v___x_2453_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2453_, 0, v___x_2451_);
                leanh::lean_ctor_set(v___x_2453_, 1, v___x_2452_);
                leanh::lean_inc(v___y_2445_);
                v___x_2454_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2454_, 0, v___y_2445_);
                leanh::lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                v___x_2455_ = 0;
                v___x_2456_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2456_, 0, v___x_2454_);
                leanh::lean_ctor_set_uint8(
                    v___x_2456_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2455_,
                );
                v___x_2457_ = l_Repr_addAppParen(v___x_2456_, v_prec_2412_);
                return v___x_2457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instReprDecl_repr___redArg___boxed(
    mut v_inst_2464_: *mut leanh::LeanObject,
    mut v_x_2465_: *mut leanh::LeanObject,
    mut v_prec_2466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2467_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_2464_, v_x_2465_, v_prec_2466_);
    leanh::lean_dec(v_prec_2466_);
    return v_res_2467_;
}
pub unsafe fn l_Std_Sat_AIG_instReprDecl_repr(
    mut v_00_u03b1_2468_: *mut leanh::LeanObject,
    mut v_inst_2469_: *mut leanh::LeanObject,
    mut v_x_2470_: *mut leanh::LeanObject,
    mut v_prec_2471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Std_Sat_AIG_instReprDecl_repr___redArg(v_inst_2469_, v_x_2470_, v_prec_2471_);
    return v___x_2472_;
}
pub unsafe fn l_Std_Sat_AIG_instReprDecl_repr___boxed(
    mut v_00_u03b1_2473_: *mut leanh::LeanObject,
    mut v_inst_2474_: *mut leanh::LeanObject,
    mut v_x_2475_: *mut leanh::LeanObject,
    mut v_prec_2476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2477_ =
        l_Std_Sat_AIG_instReprDecl_repr(v_00_u03b1_2473_, v_inst_2474_, v_x_2475_, v_prec_2476_);
    leanh::lean_dec(v_prec_2476_);
    return v_res_2477_;
}
pub unsafe fn l_Std_Sat_AIG_instReprDecl___redArg(
    mut v_inst_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_instReprDecl_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_2479_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2479_, 1, v_inst_2478_);
    return v___x_2479_;
}
pub unsafe fn l_Std_Sat_AIG_instReprDecl(
    mut v_00_u03b1_2480_: *mut leanh::LeanObject,
    mut v_inst_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_instReprDecl_repr___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_2482_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2482_, 1, v_inst_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(
    mut v_inst_2483_: *mut leanh::LeanObject,
    mut v_x_2484_: *mut leanh::LeanObject,
    mut v_x_2485_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_2484_) {
        0 => {
            leanh::lean_dec_ref(v_inst_2483_);
            if leanh::lean_obj_tag(v_x_2485_) == 0 {
                let mut v___x_2486_: u8 = 0;
                v___x_2486_ = 1;
                return v___x_2486_;
            } else {
                let mut v___x_2487_: u8 = 0;
                leanh::lean_dec(v_x_2485_);
                v___x_2487_ = 0;
                return v___x_2487_;
            }
        }
        1 => {
            let mut v_idx_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2489_: u8 = 0;
            v_idx_2488_ = leanh::lean_ctor_get(v_x_2484_, 0);
            leanh::lean_inc(v_idx_2488_);
            leanh::lean_dec_ref_known(v_x_2484_, 1);
            v___x_2489_ = 0;
            if leanh::lean_obj_tag(v_x_2485_) == 1 {
                let mut v_idx_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2492_: u8 = 0;
                v_idx_2490_ = leanh::lean_ctor_get(v_x_2485_, 0);
                leanh::lean_inc(v_idx_2490_);
                leanh::lean_dec_ref_known(v_x_2485_, 1);
                v___x_2491_ = leanh::lean_apply_2(v_inst_2483_, v_idx_2488_, v_idx_2490_);
                v___x_2492_ = (leanh::lean_unbox(v___x_2491_) as u8);
                if v___x_2492_ == 0 {
                    return v___x_2489_;
                } else {
                    let mut v___x_2493_: u8 = 0;
                    v___x_2493_ = (leanh::lean_unbox(v___x_2491_) as u8);
                    return v___x_2493_;
                }
            } else {
                leanh::lean_dec(v_idx_2488_);
                leanh::lean_dec(v_x_2485_);
                leanh::lean_dec_ref(v_inst_2483_);
                return v___x_2489_;
            }
        }
        _ => {
            let mut v_l_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2496_: u8 = 0;
            leanh::lean_dec_ref(v_inst_2483_);
            v_l_2494_ = leanh::lean_ctor_get(v_x_2484_, 0);
            leanh::lean_inc(v_l_2494_);
            v_r_2495_ = leanh::lean_ctor_get(v_x_2484_, 1);
            leanh::lean_inc(v_r_2495_);
            leanh::lean_dec_ref_known(v_x_2484_, 2);
            v___x_2496_ = 0;
            if leanh::lean_obj_tag(v_x_2485_) == 2 {
                let mut v_l_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2499_: u8 = 0;
                v_l_2497_ = leanh::lean_ctor_get(v_x_2485_, 0);
                leanh::lean_inc(v_l_2497_);
                v_r_2498_ = leanh::lean_ctor_get(v_x_2485_, 1);
                leanh::lean_inc(v_r_2498_);
                leanh::lean_dec_ref_known(v_x_2485_, 2);
                v___x_2499_ = lean_nat_dec_eq(v_l_2494_, v_l_2497_);
                leanh::lean_dec(v_l_2497_);
                leanh::lean_dec(v_l_2494_);
                if v___x_2499_ == 0 {
                    leanh::lean_dec(v_r_2498_);
                    leanh::lean_dec(v_r_2495_);
                    return v___x_2496_;
                } else {
                    let mut v___x_2500_: u8 = 0;
                    v___x_2500_ = lean_nat_dec_eq(v_r_2495_, v_r_2498_);
                    leanh::lean_dec(v_r_2498_);
                    leanh::lean_dec(v_r_2495_);
                    if v___x_2500_ == 0 {
                        return v___x_2496_;
                    } else {
                        return v___x_2500_;
                    }
                }
            } else {
                leanh::lean_dec(v_r_2495_);
                leanh::lean_dec(v_l_2494_);
                leanh::lean_dec(v_x_2485_);
                return v___x_2496_;
            }
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg___boxed(
    mut v_inst_2501_: *mut leanh::LeanObject,
    mut v_x_2502_: *mut leanh::LeanObject,
    mut v_x_2503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2504_: u8 = 0;
    let mut v_r_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2504_ =
        l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_2501_, v_x_2502_, v_x_2503_);
    v_r_2505_ = leanh::lean_box((v_res_2504_) as usize);
    return v_r_2505_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl_decEq(
    mut v_00_u03b1_2506_: *mut leanh::LeanObject,
    mut v_inst_2507_: *mut leanh::LeanObject,
    mut v_x_2508_: *mut leanh::LeanObject,
    mut v_x_2509_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2510_: u8 = 0;
    v___x_2510_ =
        l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_2507_, v_x_2508_, v_x_2509_);
    return v___x_2510_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl_decEq___boxed(
    mut v_00_u03b1_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_x_2513_: *mut leanh::LeanObject,
    mut v_x_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2515_: u8 = 0;
    let mut v_r_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Std_Sat_AIG_instDecidableEqDecl_decEq(
        v_00_u03b1_2511_,
        v_inst_2512_,
        v_x_2513_,
        v_x_2514_,
    );
    v_r_2516_ = leanh::lean_box((v_res_2515_) as usize);
    return v_r_2516_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl___redArg(
    mut v_inst_2517_: *mut leanh::LeanObject,
    mut v_x_2518_: *mut leanh::LeanObject,
    mut v_x_2519_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2520_: u8 = 0;
    v___x_2520_ =
        l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_2517_, v_x_2518_, v_x_2519_);
    return v___x_2520_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl___redArg___boxed(
    mut v_inst_2521_: *mut leanh::LeanObject,
    mut v_x_2522_: *mut leanh::LeanObject,
    mut v_x_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2524_: u8 = 0;
    let mut v_r_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2524_ = l_Std_Sat_AIG_instDecidableEqDecl___redArg(v_inst_2521_, v_x_2522_, v_x_2523_);
    v_r_2525_ = leanh::lean_box((v_res_2524_) as usize);
    return v_r_2525_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl(
    mut v_00_u03b1_2526_: *mut leanh::LeanObject,
    mut v_inst_2527_: *mut leanh::LeanObject,
    mut v_x_2528_: *mut leanh::LeanObject,
    mut v_x_2529_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2530_: u8 = 0;
    v___x_2530_ =
        l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_2527_, v_x_2528_, v_x_2529_);
    return v___x_2530_;
}
pub unsafe fn l_Std_Sat_AIG_instDecidableEqDecl___boxed(
    mut v_00_u03b1_2531_: *mut leanh::LeanObject,
    mut v_inst_2532_: *mut leanh::LeanObject,
    mut v_x_2533_: *mut leanh::LeanObject,
    mut v_x_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2535_: u8 = 0;
    let mut v_r_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2535_ =
        l_Std_Sat_AIG_instDecidableEqDecl(v_00_u03b1_2531_, v_inst_2532_, v_x_2533_, v_x_2534_);
    v_r_2536_ = leanh::lean_box((v_res_2535_) as usize);
    return v_r_2536_;
}
pub unsafe fn l_Std_Sat_AIG_instInhabitedDecl_default(
    mut v_00_u03b1_2537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2538_ = leanh::lean_box(0);
    return v___x_2538_;
}
pub unsafe fn l_Std_Sat_AIG_instInhabitedDecl(
    mut v_a_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = leanh::lean_box(0);
    return v___x_2540_;
}
pub unsafe fn _init_l_Std_Sat_AIG_Cache_empty___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = leanh::lean_box(0);
    v___x_2542_ = leanh::lean_unsigned_to_nat(16);
    v___x_2543_ = lean_mk_array(v___x_2542_, v___x_2541_);
    return v___x_2543_;
}
pub unsafe fn _init_l_Std_Sat_AIG_Cache_empty___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_Cache_empty___closed__0),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_Cache_empty___closed__0_once),
        _init_l_Std_Sat_AIG_Cache_empty___closed__0,
    );
    v___x_2545_ = leanh::lean_unsigned_to_nat(0);
    v___x_2546_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2546_, 0, v___x_2545_);
    leanh::lean_ctor_set(v___x_2546_, 1, v___x_2544_);
    return v___x_2546_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_empty(
    mut v_00_u03b1_2547_: *mut leanh::LeanObject,
    mut v_inst_2548_: *mut leanh::LeanObject,
    mut v_inst_2549_: *mut leanh::LeanObject,
    mut v_decls_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2551_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_Cache_empty___closed__1),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_Cache_empty___closed__1_once),
        _init_l_Std_Sat_AIG_Cache_empty___closed__1,
    );
    return v___x_2551_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_empty___boxed(
    mut v_00_u03b1_2552_: *mut leanh::LeanObject,
    mut v_inst_2553_: *mut leanh::LeanObject,
    mut v_inst_2554_: *mut leanh::LeanObject,
    mut v_decls_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ =
        l_Std_Sat_AIG_Cache_empty(v_00_u03b1_2552_, v_inst_2553_, v_inst_2554_, v_decls_2555_);
    leanh::lean_dec_ref(v_decls_2555_);
    leanh::lean_dec_ref(v_inst_2554_);
    leanh::lean_dec_ref(v_inst_2553_);
    return v_res_2556_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_noUpdate___redArg(
    mut v_cache_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_cache_2557_);
    return v_cache_2557_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_noUpdate___redArg___boxed(
    mut v_cache_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Std_Sat_AIG_Cache_noUpdate___redArg(v_cache_2558_);
    leanh::lean_dec_ref(v_cache_2558_);
    return v_res_2559_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_noUpdate(
    mut v_00_u03b1_2560_: *mut leanh::LeanObject,
    mut v_inst_2561_: *mut leanh::LeanObject,
    mut v_inst_2562_: *mut leanh::LeanObject,
    mut v_decls_2563_: *mut leanh::LeanObject,
    mut v_decl_2564_: *mut leanh::LeanObject,
    mut v_cache_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_cache_2565_);
    return v_cache_2565_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_noUpdate___boxed(
    mut v_00_u03b1_2566_: *mut leanh::LeanObject,
    mut v_inst_2567_: *mut leanh::LeanObject,
    mut v_inst_2568_: *mut leanh::LeanObject,
    mut v_decls_2569_: *mut leanh::LeanObject,
    mut v_decl_2570_: *mut leanh::LeanObject,
    mut v_cache_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2572_ = l_Std_Sat_AIG_Cache_noUpdate(
        v_00_u03b1_2566_,
        v_inst_2567_,
        v_inst_2568_,
        v_decls_2569_,
        v_decl_2570_,
        v_cache_2571_,
    );
    leanh::lean_dec_ref(v_cache_2571_);
    leanh::lean_dec(v_decl_2570_);
    leanh::lean_dec_ref(v_decls_2569_);
    leanh::lean_dec_ref(v_inst_2568_);
    leanh::lean_dec_ref(v_inst_2567_);
    return v_res_2572_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_insert___redArg___lam__0(
    mut v_inst_2573_: *mut leanh::LeanObject,
    mut v_a_2574_: *mut leanh::LeanObject,
    mut v_b_2575_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2576_: u8 = 0;
    v___x_2576_ =
        l_Std_Sat_AIG_instDecidableEqDecl_decEq___redArg(v_inst_2573_, v_a_2574_, v_b_2575_);
    return v___x_2576_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed(
    mut v_inst_2577_: *mut leanh::LeanObject,
    mut v_a_2578_: *mut leanh::LeanObject,
    mut v_b_2579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2580_: u8 = 0;
    let mut v_r_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2580_ = l_Std_Sat_AIG_Cache_insert___redArg___lam__0(v_inst_2577_, v_a_2578_, v_b_2579_);
    v_r_2581_ = leanh::lean_box((v_res_2580_) as usize);
    return v_r_2581_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_insert___redArg(
    mut v_inst_2582_: *mut leanh::LeanObject,
    mut v_inst_2583_: *mut leanh::LeanObject,
    mut v_decls_2584_: *mut leanh::LeanObject,
    mut v_cache_2585_: *mut leanh::LeanObject,
    mut v_decl_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2587_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2587_, 0, v_inst_2583_);
    v___x_2588_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_2588_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2588_, 1, v_inst_2582_);
    v___f_2589_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2589_, 0, v___f_2587_);
    v___x_2590_ = lean_array_get_size(v_decls_2584_);
    v___x_2591_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___f_2589_,
        v___x_2588_,
        v_cache_2585_,
        v_decl_2586_,
        v___x_2590_,
    );
    return v___x_2591_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_insert___redArg___boxed(
    mut v_inst_2592_: *mut leanh::LeanObject,
    mut v_inst_2593_: *mut leanh::LeanObject,
    mut v_decls_2594_: *mut leanh::LeanObject,
    mut v_cache_2595_: *mut leanh::LeanObject,
    mut v_decl_2596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2597_ = l_Std_Sat_AIG_Cache_insert___redArg(
        v_inst_2592_,
        v_inst_2593_,
        v_decls_2594_,
        v_cache_2595_,
        v_decl_2596_,
    );
    leanh::lean_dec_ref(v_decls_2594_);
    return v_res_2597_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_insert(
    mut v_00_u03b1_2598_: *mut leanh::LeanObject,
    mut v_inst_2599_: *mut leanh::LeanObject,
    mut v_inst_2600_: *mut leanh::LeanObject,
    mut v_decls_2601_: *mut leanh::LeanObject,
    mut v_cache_2602_: *mut leanh::LeanObject,
    mut v_decl_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2604_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2604_, 0, v_inst_2600_);
    v___x_2605_ = leanh::lean_alloc_closure(
        l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_2605_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2605_, 1, v_inst_2599_);
    v___f_2606_ = leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2606_, 0, v___f_2604_);
    v___x_2607_ = lean_array_get_size(v_decls_2601_);
    v___x_2608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        v___f_2606_,
        v___x_2605_,
        v_cache_2602_,
        v_decl_2603_,
        v___x_2607_,
    );
    return v___x_2608_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_insert___boxed(
    mut v_00_u03b1_2609_: *mut leanh::LeanObject,
    mut v_inst_2610_: *mut leanh::LeanObject,
    mut v_inst_2611_: *mut leanh::LeanObject,
    mut v_decls_2612_: *mut leanh::LeanObject,
    mut v_cache_2613_: *mut leanh::LeanObject,
    mut v_decl_2614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2615_ = l_Std_Sat_AIG_Cache_insert(
        v_00_u03b1_2609_,
        v_inst_2610_,
        v_inst_2611_,
        v_decls_2612_,
        v_cache_2613_,
        v_decl_2614_,
    );
    leanh::lean_dec_ref(v_decls_2612_);
    return v_res_2615_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_get_x3f___redArg(
    mut v_inst_2616_: *mut leanh::LeanObject,
    mut v_inst_2617_: *mut leanh::LeanObject,
    mut v_cache_2618_: *mut leanh::LeanObject,
    mut v_decl_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2620_ = leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_2620_, 0, v_inst_2617_);
                v___x_2621_ = leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___x_2621_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2621_, 1, v_inst_2616_);
                v___f_2622_ = leanh::lean_alloc_closure(
                    l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_2622_, 0, v___f_2620_);
                v___x_2623_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___f_2622_,
                    v___x_2621_,
                    v_cache_2618_,
                    v_decl_2619_,
                );
                if leanh::lean_obj_tag(v___x_2623_) == 0 {
                    v___x_2624_ = leanh::lean_box(0);
                    return v___x_2624_;
                } else {
                    v_val_2625_ = leanh::lean_ctor_get(v___x_2623_, 0);
                    v_isSharedCheck_2632_ = (!leanh::lean_is_exclusive(v___x_2623_)) as u8;
                    if v_isSharedCheck_2632_ == 0 {
                        v___x_2627_ = v___x_2623_;
                        v_isShared_2628_ = v_isSharedCheck_2632_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2625_);
                        leanh::lean_dec(v___x_2623_);
                        v___x_2627_ = leanh::lean_box(0);
                        v_isShared_2628_ = v_isSharedCheck_2632_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2628_ == 0 {
                    v___x_2630_ = v___x_2627_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_val_2625_);
                    v___x_2630_ = v_reuseFailAlloc_2631_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Cache_get_x3f___redArg___boxed(
    mut v_inst_2633_: *mut leanh::LeanObject,
    mut v_inst_2634_: *mut leanh::LeanObject,
    mut v_cache_2635_: *mut leanh::LeanObject,
    mut v_decl_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2637_ = l_Std_Sat_AIG_Cache_get_x3f___redArg(
        v_inst_2633_,
        v_inst_2634_,
        v_cache_2635_,
        v_decl_2636_,
    );
    leanh::lean_dec_ref(v_cache_2635_);
    return v_res_2637_;
}
pub unsafe fn l_Std_Sat_AIG_Cache_get_x3f(
    mut v_00_u03b1_2638_: *mut leanh::LeanObject,
    mut v_inst_2639_: *mut leanh::LeanObject,
    mut v_inst_2640_: *mut leanh::LeanObject,
    mut v_decls_2641_: *mut leanh::LeanObject,
    mut v_cache_2642_: *mut leanh::LeanObject,
    mut v_decl_2643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2644_ = leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_Cache_insert___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_2644_, 0, v_inst_2640_);
                v___x_2645_ = leanh::lean_alloc_closure(
                    l_Std_Sat_AIG_instHashableDecl_hash___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___x_2645_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2645_, 1, v_inst_2639_);
                v___f_2646_ = leanh::lean_alloc_closure(
                    l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_2646_, 0, v___f_2644_);
                v___x_2647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(
                    v___f_2646_,
                    v___x_2645_,
                    v_cache_2642_,
                    v_decl_2643_,
                );
                if leanh::lean_obj_tag(v___x_2647_) == 0 {
                    v___x_2648_ = leanh::lean_box(0);
                    return v___x_2648_;
                } else {
                    v_val_2649_ = leanh::lean_ctor_get(v___x_2647_, 0);
                    v_isSharedCheck_2656_ = (!leanh::lean_is_exclusive(v___x_2647_)) as u8;
                    if v_isSharedCheck_2656_ == 0 {
                        v___x_2651_ = v___x_2647_;
                        v_isShared_2652_ = v_isSharedCheck_2656_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2649_);
                        leanh::lean_dec(v___x_2647_);
                        v___x_2651_ = leanh::lean_box(0);
                        v_isShared_2652_ = v_isSharedCheck_2656_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2652_ == 0 {
                    v___x_2654_ = v___x_2651_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_val_2649_);
                    v___x_2654_ = v_reuseFailAlloc_2655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Cache_get_x3f___boxed(
    mut v_00_u03b1_2657_: *mut leanh::LeanObject,
    mut v_inst_2658_: *mut leanh::LeanObject,
    mut v_inst_2659_: *mut leanh::LeanObject,
    mut v_decls_2660_: *mut leanh::LeanObject,
    mut v_cache_2661_: *mut leanh::LeanObject,
    mut v_decl_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2663_ = l_Std_Sat_AIG_Cache_get_x3f(
        v_00_u03b1_2657_,
        v_inst_2658_,
        v_inst_2659_,
        v_decls_2660_,
        v_cache_2661_,
        v_decl_2662_,
    );
    leanh::lean_dec_ref(v_cache_2661_);
    leanh::lean_dec_ref(v_decls_2660_);
    return v_res_2663_;
}
pub unsafe fn _init_l_Std_Sat_AIG_empty___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_Cache_empty___closed__1),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_Cache_empty___closed__1_once),
        _init_l_Std_Sat_AIG_Cache_empty___closed__1,
    );
    v___x_2669_ = l_Std_Sat_AIG_empty___closed__0;
    v___x_2670_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2670_, 0, v___x_2669_);
    leanh::lean_ctor_set(v___x_2670_, 1, v___x_2668_);
    return v___x_2670_;
}
pub unsafe fn l_Std_Sat_AIG_empty(
    mut v_00_u03b1_2671_: *mut leanh::LeanObject,
    mut v_inst_2672_: *mut leanh::LeanObject,
    mut v_inst_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2674_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___closed__1),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_empty___closed__1_once),
        _init_l_Std_Sat_AIG_empty___closed__1,
    );
    return v___x_2674_;
}
pub unsafe fn l_Std_Sat_AIG_empty___boxed(
    mut v_00_u03b1_2675_: *mut leanh::LeanObject,
    mut v_inst_2676_: *mut leanh::LeanObject,
    mut v_inst_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Std_Sat_AIG_empty(v_00_u03b1_2675_, v_inst_2676_, v_inst_2677_);
    leanh::lean_dec_ref(v_inst_2677_);
    leanh::lean_dec_ref(v_inst_2676_);
    return v_res_2678_;
}
pub unsafe fn l_Std_Sat_AIG_instMembership(
    mut v_00_u03b1_2679_: *mut leanh::LeanObject,
    mut v_inst_2680_: *mut leanh::LeanObject,
    mut v_inst_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = leanh::lean_box(0);
    return v___x_2682_;
}
pub unsafe fn l_Std_Sat_AIG_instMembership___boxed(
    mut v_00_u03b1_2683_: *mut leanh::LeanObject,
    mut v_inst_2684_: *mut leanh::LeanObject,
    mut v_inst_2685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2686_ = l_Std_Sat_AIG_instMembership(v_00_u03b1_2683_, v_inst_2684_, v_inst_2685_);
    leanh::lean_dec_ref(v_inst_2685_);
    leanh::lean_dec_ref(v_inst_2684_);
    return v_res_2686_;
}
pub unsafe fn l_Std_Sat_AIG_Ref_cast___redArg(
    mut v_ref_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2689_: u8 = 0;
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gate_2688_ = leanh::lean_ctor_get(v_ref_2687_, 0);
                v_invert_2689_ = leanh::lean_ctor_get_uint8(
                    v_ref_2687_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2696_ = (!leanh::lean_is_exclusive(v_ref_2687_)) as u8;
                if v_isSharedCheck_2696_ == 0 {
                    v___x_2691_ = v_ref_2687_;
                    v_isShared_2692_ = v_isSharedCheck_2696_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2688_);
                    leanh::lean_dec(v_ref_2687_);
                    v___x_2691_ = leanh::lean_box(0);
                    v_isShared_2692_ = v_isSharedCheck_2696_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2692_ == 0 {
                    v___x_2694_ = v___x_2691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2695_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_gate_2688_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2695_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_2689_,
                    );
                    v___x_2694_ = v_reuseFailAlloc_2695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Ref_cast(
    mut v_00_u03b1_2697_: *mut leanh::LeanObject,
    mut v_inst_2698_: *mut leanh::LeanObject,
    mut v_inst_2699_: *mut leanh::LeanObject,
    mut v_aig1_2700_: *mut leanh::LeanObject,
    mut v_aig2_2701_: *mut leanh::LeanObject,
    mut v_ref_2702_: *mut leanh::LeanObject,
    mut v_h_2703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2705_: u8 = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2708_: u8 = 0;
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2712_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gate_2704_ = leanh::lean_ctor_get(v_ref_2702_, 0);
                v_invert_2705_ = leanh::lean_ctor_get_uint8(
                    v_ref_2702_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2712_ = (!leanh::lean_is_exclusive(v_ref_2702_)) as u8;
                if v_isSharedCheck_2712_ == 0 {
                    v___x_2707_ = v_ref_2702_;
                    v_isShared_2708_ = v_isSharedCheck_2712_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2704_);
                    leanh::lean_dec(v_ref_2702_);
                    v___x_2707_ = leanh::lean_box(0);
                    v_isShared_2708_ = v_isSharedCheck_2712_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2708_ == 0 {
                    v___x_2710_ = v___x_2707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2711_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_gate_2704_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2711_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_2705_,
                    );
                    v___x_2710_ = v_reuseFailAlloc_2711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Ref_cast___boxed(
    mut v_00_u03b1_2713_: *mut leanh::LeanObject,
    mut v_inst_2714_: *mut leanh::LeanObject,
    mut v_inst_2715_: *mut leanh::LeanObject,
    mut v_aig1_2716_: *mut leanh::LeanObject,
    mut v_aig2_2717_: *mut leanh::LeanObject,
    mut v_ref_2718_: *mut leanh::LeanObject,
    mut v_h_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2720_ = l_Std_Sat_AIG_Ref_cast(
        v_00_u03b1_2713_,
        v_inst_2714_,
        v_inst_2715_,
        v_aig1_2716_,
        v_aig2_2717_,
        v_ref_2718_,
        v_h_2719_,
    );
    leanh::lean_dec_ref(v_aig2_2717_);
    leanh::lean_dec_ref(v_aig1_2716_);
    leanh::lean_dec_ref(v_inst_2715_);
    leanh::lean_dec_ref(v_inst_2714_);
    return v_res_2720_;
}
pub unsafe fn l_Std_Sat_AIG_Ref_flip___redArg(
    mut v_ref_2721_: *mut leanh::LeanObject,
    mut v_inv_2722_: u8,
) -> *mut leanh::LeanObject {
    let mut v_gate_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2724_: u8 = 0;
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: u8 = 0;
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: u8 = 0;
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gate_2723_ = leanh::lean_ctor_get(v_ref_2721_, 0);
                v_invert_2724_ = leanh::lean_ctor_get_uint8(
                    v_ref_2721_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2736_ = (!leanh::lean_is_exclusive(v_ref_2721_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v___x_2726_ = v_ref_2721_;
                    v_isShared_2727_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2723_);
                    leanh::lean_dec(v_ref_2721_);
                    v___x_2726_ = leanh::lean_box(0);
                    v_isShared_2727_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_inv_2722_ == 0 {
                    if v_invert_2724_ == 0 {
                        leanh::lean_del_object(v___x_2726_);
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    if v_invert_2724_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2726_);
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2729_ = 1;
                if v_isShared_2727_ == 0 {
                    v___x_2731_ = v___x_2726_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_gate_2723_);
                    v___x_2731_ = v_reuseFailAlloc_2732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2731_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2729_,
                );
                return v___x_2731_;
            }
            4 => {
                v___x_2734_ = 0;
                v___x_2735_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2735_, 0, v_gate_2723_);
                leanh::lean_ctor_set_uint8(
                    v___x_2735_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2734_,
                );
                return v___x_2735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Ref_flip___redArg___boxed(
    mut v_ref_2737_: *mut leanh::LeanObject,
    mut v_inv_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inv_boxed_2739_: u8 = 0;
    let mut v_res_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inv_boxed_2739_ = (leanh::lean_unbox(v_inv_2738_) as u8);
    v_res_2740_ = l_Std_Sat_AIG_Ref_flip___redArg(v_ref_2737_, v_inv_boxed_2739_);
    return v_res_2740_;
}
pub unsafe fn l_Std_Sat_AIG_Ref_flip(
    mut v_00_u03b1_2741_: *mut leanh::LeanObject,
    mut v_inst_2742_: *mut leanh::LeanObject,
    mut v_inst_2743_: *mut leanh::LeanObject,
    mut v_aig_2744_: *mut leanh::LeanObject,
    mut v_ref_2745_: *mut leanh::LeanObject,
    mut v_inv_2746_: u8,
) -> *mut leanh::LeanObject {
    let mut v_gate_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2748_: u8 = 0;
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2753_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: u8 = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gate_2747_ = leanh::lean_ctor_get(v_ref_2745_, 0);
                v_invert_2748_ = leanh::lean_ctor_get_uint8(
                    v_ref_2745_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2760_ = (!leanh::lean_is_exclusive(v_ref_2745_)) as u8;
                if v_isSharedCheck_2760_ == 0 {
                    v___x_2750_ = v_ref_2745_;
                    v_isShared_2751_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2747_);
                    leanh::lean_dec(v_ref_2745_);
                    v___x_2750_ = leanh::lean_box(0);
                    v_isShared_2751_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_inv_2746_ == 0 {
                    if v_invert_2748_ == 0 {
                        leanh::lean_del_object(v___x_2750_);
                        state = 4;
                        continue;
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    if v_invert_2748_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2750_);
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2753_ = 1;
                if v_isShared_2751_ == 0 {
                    v___x_2755_ = v___x_2750_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_gate_2747_);
                    v___x_2755_ = v_reuseFailAlloc_2756_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2755_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2753_,
                );
                return v___x_2755_;
            }
            4 => {
                v___x_2758_ = 0;
                v___x_2759_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2759_, 0, v_gate_2747_);
                leanh::lean_ctor_set_uint8(
                    v___x_2759_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2758_,
                );
                return v___x_2759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Ref_flip___boxed(
    mut v_00_u03b1_2761_: *mut leanh::LeanObject,
    mut v_inst_2762_: *mut leanh::LeanObject,
    mut v_inst_2763_: *mut leanh::LeanObject,
    mut v_aig_2764_: *mut leanh::LeanObject,
    mut v_ref_2765_: *mut leanh::LeanObject,
    mut v_inv_2766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inv_boxed_2767_: u8 = 0;
    let mut v_res_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_inv_boxed_2767_ = (leanh::lean_unbox(v_inv_2766_) as u8);
    v_res_2768_ = l_Std_Sat_AIG_Ref_flip(
        v_00_u03b1_2761_,
        v_inst_2762_,
        v_inst_2763_,
        v_aig_2764_,
        v_ref_2765_,
        v_inv_boxed_2767_,
    );
    leanh::lean_dec_ref(v_aig_2764_);
    leanh::lean_dec_ref(v_inst_2763_);
    leanh::lean_dec_ref(v_inst_2762_);
    return v_res_2768_;
}
pub unsafe fn l_Std_Sat_AIG_Ref_not___redArg(
    mut v_ref_2769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_invert_2770_: u8 = 0;
    let mut v_gate_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2774_: u8 = 0;
    let mut v___x_2775_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_gate_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2784_: u8 = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_invert_2770_ = leanh::lean_ctor_get_uint8(
                    v_ref_2769_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_2770_ == 0 {
                    v_gate_2771_ = leanh::lean_ctor_get(v_ref_2769_, 0);
                    v_isSharedCheck_2779_ = (!leanh::lean_is_exclusive(v_ref_2769_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2773_ = v_ref_2769_;
                        v_isShared_2774_ = v_isSharedCheck_2779_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_2771_);
                        leanh::lean_dec(v_ref_2769_);
                        v___x_2773_ = leanh::lean_box(0);
                        v_isShared_2774_ = v_isSharedCheck_2779_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_gate_2780_ = leanh::lean_ctor_get(v_ref_2769_, 0);
                    v_isSharedCheck_2788_ = (!leanh::lean_is_exclusive(v_ref_2769_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2782_ = v_ref_2769_;
                        v_isShared_2783_ = v_isSharedCheck_2788_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_2780_);
                        leanh::lean_dec(v_ref_2769_);
                        v___x_2782_ = leanh::lean_box(0);
                        v_isShared_2783_ = v_isSharedCheck_2788_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2775_ = 1;
                if v_isShared_2774_ == 0 {
                    v___x_2777_ = v___x_2773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_gate_2771_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2777_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2775_,
                );
                return v___x_2777_;
            }
            3 => {
                v___x_2784_ = 0;
                if v_isShared_2783_ == 0 {
                    v___x_2786_ = v___x_2782_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2787_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_gate_2780_);
                    v___x_2786_ = v_reuseFailAlloc_2787_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2786_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2784_,
                );
                return v___x_2786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Ref_not(
    mut v_00_u03b1_2789_: *mut leanh::LeanObject,
    mut v_inst_2790_: *mut leanh::LeanObject,
    mut v_inst_2791_: *mut leanh::LeanObject,
    mut v_aig_2792_: *mut leanh::LeanObject,
    mut v_ref_2793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_invert_2794_: u8 = 0;
    let mut v_gate_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2798_: u8 = 0;
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2803_: u8 = 0;
    let mut v_gate_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2807_: u8 = 0;
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_invert_2794_ = leanh::lean_ctor_get_uint8(
                    v_ref_2793_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_2794_ == 0 {
                    v_gate_2795_ = leanh::lean_ctor_get(v_ref_2793_, 0);
                    v_isSharedCheck_2803_ = (!leanh::lean_is_exclusive(v_ref_2793_)) as u8;
                    if v_isSharedCheck_2803_ == 0 {
                        v___x_2797_ = v_ref_2793_;
                        v_isShared_2798_ = v_isSharedCheck_2803_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_2795_);
                        leanh::lean_dec(v_ref_2793_);
                        v___x_2797_ = leanh::lean_box(0);
                        v_isShared_2798_ = v_isSharedCheck_2803_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_gate_2804_ = leanh::lean_ctor_get(v_ref_2793_, 0);
                    v_isSharedCheck_2812_ = (!leanh::lean_is_exclusive(v_ref_2793_)) as u8;
                    if v_isSharedCheck_2812_ == 0 {
                        v___x_2806_ = v_ref_2793_;
                        v_isShared_2807_ = v_isSharedCheck_2812_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_2804_);
                        leanh::lean_dec(v_ref_2793_);
                        v___x_2806_ = leanh::lean_box(0);
                        v_isShared_2807_ = v_isSharedCheck_2812_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2799_ = 1;
                if v_isShared_2798_ == 0 {
                    v___x_2801_ = v___x_2797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_gate_2795_);
                    v___x_2801_ = v_reuseFailAlloc_2802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2801_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2799_,
                );
                return v___x_2801_;
            }
            3 => {
                v___x_2808_ = 0;
                if v_isShared_2807_ == 0 {
                    v___x_2810_ = v___x_2806_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2811_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_gate_2804_);
                    v___x_2810_ = v_reuseFailAlloc_2811_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2810_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2808_,
                );
                return v___x_2810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_Ref_not___boxed(
    mut v_00_u03b1_2813_: *mut leanh::LeanObject,
    mut v_inst_2814_: *mut leanh::LeanObject,
    mut v_inst_2815_: *mut leanh::LeanObject,
    mut v_aig_2816_: *mut leanh::LeanObject,
    mut v_ref_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2818_ = l_Std_Sat_AIG_Ref_not(
        v_00_u03b1_2813_,
        v_inst_2814_,
        v_inst_2815_,
        v_aig_2816_,
        v_ref_2817_,
    );
    leanh::lean_dec_ref(v_aig_2816_);
    leanh::lean_dec_ref(v_inst_2815_);
    leanh::lean_dec_ref(v_inst_2814_);
    return v_res_2818_;
}
pub unsafe fn l_Std_Sat_AIG_BinaryInput_cast___redArg(
    mut v_input_2819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v_gate_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2826_: u8 = 0;
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2829_: u8 = 0;
    let mut v_gate_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2831_: u8 = 0;
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2834_: u8 = 0;
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2820_ = leanh::lean_ctor_get(v_input_2819_, 0);
                v_rhs_2821_ = leanh::lean_ctor_get(v_input_2819_, 1);
                v_isSharedCheck_2846_ = (!leanh::lean_is_exclusive(v_input_2819_)) as u8;
                if v_isSharedCheck_2846_ == 0 {
                    v___x_2823_ = v_input_2819_;
                    v_isShared_2824_ = v_isSharedCheck_2846_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_2821_);
                    leanh::lean_inc(v_lhs_2820_);
                    leanh::lean_dec(v_input_2819_);
                    v___x_2823_ = leanh::lean_box(0);
                    v_isShared_2824_ = v_isSharedCheck_2846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_2825_ = leanh::lean_ctor_get(v_lhs_2820_, 0);
                v_invert_2826_ = leanh::lean_ctor_get_uint8(
                    v_lhs_2820_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2845_ = (!leanh::lean_is_exclusive(v_lhs_2820_)) as u8;
                if v_isSharedCheck_2845_ == 0 {
                    v___x_2828_ = v_lhs_2820_;
                    v_isShared_2829_ = v_isSharedCheck_2845_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2825_);
                    leanh::lean_dec(v_lhs_2820_);
                    v___x_2828_ = leanh::lean_box(0);
                    v_isShared_2829_ = v_isSharedCheck_2845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_2830_ = leanh::lean_ctor_get(v_rhs_2821_, 0);
                v_invert_2831_ = leanh::lean_ctor_get_uint8(
                    v_rhs_2821_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2844_ = (!leanh::lean_is_exclusive(v_rhs_2821_)) as u8;
                if v_isSharedCheck_2844_ == 0 {
                    v___x_2833_ = v_rhs_2821_;
                    v_isShared_2834_ = v_isSharedCheck_2844_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2830_);
                    leanh::lean_dec(v_rhs_2821_);
                    v___x_2833_ = leanh::lean_box(0);
                    v_isShared_2834_ = v_isSharedCheck_2844_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2834_ == 0 {
                    leanh::lean_ctor_set(v___x_2833_, 0, v_gate_2825_);
                    v___x_2836_ = v___x_2833_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_gate_2825_);
                    v___x_2836_ = v_reuseFailAlloc_2843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2836_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_2826_,
                );
                if v_isShared_2829_ == 0 {
                    leanh::lean_ctor_set(v___x_2828_, 0, v_gate_2830_);
                    v___x_2838_ = v___x_2828_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2842_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_gate_2830_);
                    v___x_2838_ = v_reuseFailAlloc_2842_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2838_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_2831_,
                );
                if v_isShared_2824_ == 0 {
                    leanh::lean_ctor_set(v___x_2823_, 1, v___x_2838_);
                    leanh::lean_ctor_set(v___x_2823_, 0, v___x_2836_);
                    v___x_2840_ = v___x_2823_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2841_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___x_2838_);
                    v___x_2840_ = v_reuseFailAlloc_2841_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_BinaryInput_cast(
    mut v_00_u03b1_2847_: *mut leanh::LeanObject,
    mut v_inst_2848_: *mut leanh::LeanObject,
    mut v_inst_2849_: *mut leanh::LeanObject,
    mut v_aig1_2850_: *mut leanh::LeanObject,
    mut v_aig2_2851_: *mut leanh::LeanObject,
    mut v_input_2852_: *mut leanh::LeanObject,
    mut v_h_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2858_: u8 = 0;
    let mut v_gate_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2860_: u8 = 0;
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v_gate_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2865_: u8 = 0;
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2868_: u8 = 0;
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_isSharedCheck_2880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2854_ = leanh::lean_ctor_get(v_input_2852_, 0);
                v_rhs_2855_ = leanh::lean_ctor_get(v_input_2852_, 1);
                v_isSharedCheck_2880_ = (!leanh::lean_is_exclusive(v_input_2852_)) as u8;
                if v_isSharedCheck_2880_ == 0 {
                    v___x_2857_ = v_input_2852_;
                    v_isShared_2858_ = v_isSharedCheck_2880_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_2855_);
                    leanh::lean_inc(v_lhs_2854_);
                    leanh::lean_dec(v_input_2852_);
                    v___x_2857_ = leanh::lean_box(0);
                    v_isShared_2858_ = v_isSharedCheck_2880_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_2859_ = leanh::lean_ctor_get(v_lhs_2854_, 0);
                v_invert_2860_ = leanh::lean_ctor_get_uint8(
                    v_lhs_2854_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2879_ = (!leanh::lean_is_exclusive(v_lhs_2854_)) as u8;
                if v_isSharedCheck_2879_ == 0 {
                    v___x_2862_ = v_lhs_2854_;
                    v_isShared_2863_ = v_isSharedCheck_2879_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2859_);
                    leanh::lean_dec(v_lhs_2854_);
                    v___x_2862_ = leanh::lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2879_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_2864_ = leanh::lean_ctor_get(v_rhs_2855_, 0);
                v_invert_2865_ = leanh::lean_ctor_get_uint8(
                    v_rhs_2855_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2878_ = (!leanh::lean_is_exclusive(v_rhs_2855_)) as u8;
                if v_isSharedCheck_2878_ == 0 {
                    v___x_2867_ = v_rhs_2855_;
                    v_isShared_2868_ = v_isSharedCheck_2878_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2864_);
                    leanh::lean_dec(v_rhs_2855_);
                    v___x_2867_ = leanh::lean_box(0);
                    v_isShared_2868_ = v_isSharedCheck_2878_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2868_ == 0 {
                    leanh::lean_ctor_set(v___x_2867_, 0, v_gate_2859_);
                    v___x_2870_ = v___x_2867_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_gate_2859_);
                    v___x_2870_ = v_reuseFailAlloc_2877_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2870_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_2860_,
                );
                if v_isShared_2863_ == 0 {
                    leanh::lean_ctor_set(v___x_2862_, 0, v_gate_2864_);
                    v___x_2872_ = v___x_2862_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2876_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_gate_2864_);
                    v___x_2872_ = v_reuseFailAlloc_2876_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2872_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_2865_,
                );
                if v_isShared_2858_ == 0 {
                    leanh::lean_ctor_set(v___x_2857_, 1, v___x_2872_);
                    leanh::lean_ctor_set(v___x_2857_, 0, v___x_2870_);
                    v___x_2874_ = v___x_2857_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2875_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2875_, 1, v___x_2872_);
                    v___x_2874_ = v_reuseFailAlloc_2875_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_BinaryInput_cast___boxed(
    mut v_00_u03b1_2881_: *mut leanh::LeanObject,
    mut v_inst_2882_: *mut leanh::LeanObject,
    mut v_inst_2883_: *mut leanh::LeanObject,
    mut v_aig1_2884_: *mut leanh::LeanObject,
    mut v_aig2_2885_: *mut leanh::LeanObject,
    mut v_input_2886_: *mut leanh::LeanObject,
    mut v_h_2887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2888_ = l_Std_Sat_AIG_BinaryInput_cast(
        v_00_u03b1_2881_,
        v_inst_2882_,
        v_inst_2883_,
        v_aig1_2884_,
        v_aig2_2885_,
        v_input_2886_,
        v_h_2887_,
    );
    leanh::lean_dec_ref(v_aig2_2885_);
    leanh::lean_dec_ref(v_aig1_2884_);
    leanh::lean_dec_ref(v_inst_2883_);
    leanh::lean_dec_ref(v_inst_2882_);
    return v_res_2888_;
}
pub unsafe fn l_Std_Sat_AIG_BinaryInput_invert___redArg(
    mut v_input_2889_: *mut leanh::LeanObject,
    mut v_linv_2890_: u8,
    mut v_rinv_2891_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: u8 = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2908_: u8 = 0;
    let mut v_gate_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2911_: u8 = 0;
    let mut v_gate_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2915_: u8 = 0;
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v___x_2920_: u8 = 0;
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: u8 = 0;
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2904_ = leanh::lean_ctor_get(v_input_2889_, 0);
                leanh::lean_inc_ref(v_lhs_2904_);
                v_rhs_2905_ = leanh::lean_ctor_get(v_input_2889_, 1);
                leanh::lean_inc_ref(v_rhs_2905_);
                leanh::lean_dec_ref(v_input_2889_);
                v_gate_2914_ = leanh::lean_ctor_get(v_lhs_2904_, 0);
                v_invert_2915_ = leanh::lean_ctor_get_uint8(
                    v_lhs_2904_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2927_ = (!leanh::lean_is_exclusive(v_lhs_2904_)) as u8;
                if v_isSharedCheck_2927_ == 0 {
                    v___x_2917_ = v_lhs_2904_;
                    v_isShared_2918_ = v_isSharedCheck_2927_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2914_);
                    leanh::lean_dec(v_lhs_2904_);
                    v___x_2917_ = leanh::lean_box(0);
                    v_isShared_2918_ = v_isSharedCheck_2927_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_2895_ = 0;
                v___x_2896_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2896_, 0, v___y_2893_);
                leanh::lean_ctor_set_uint8(
                    v___x_2896_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2895_,
                );
                v___x_2897_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2897_, 0, v___y_2894_);
                leanh::lean_ctor_set(v___x_2897_, 1, v___x_2896_);
                return v___x_2897_;
            }
            2 => {
                v___x_2901_ = 1;
                v___x_2902_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2902_, 0, v___y_2899_);
                leanh::lean_ctor_set_uint8(
                    v___x_2902_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2901_,
                );
                v___x_2903_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2903_, 0, v___y_2900_);
                leanh::lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                return v___x_2903_;
            }
            3 => {
                if v_rinv_2891_ == 0 {
                    v_invert_2908_ = leanh::lean_ctor_get_uint8(
                        v_rhs_2905_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_invert_2908_ == 0 {
                        v_gate_2909_ = leanh::lean_ctor_get(v_rhs_2905_, 0);
                        leanh::lean_inc(v_gate_2909_);
                        leanh::lean_dec_ref(v_rhs_2905_);
                        v___y_2893_ = v_gate_2909_;
                        v___y_2894_ = v___y_2907_;
                        state = 1;
                        continue;
                    } else {
                        v_gate_2910_ = leanh::lean_ctor_get(v_rhs_2905_, 0);
                        leanh::lean_inc(v_gate_2910_);
                        leanh::lean_dec_ref(v_rhs_2905_);
                        v___y_2899_ = v_gate_2910_;
                        v___y_2900_ = v___y_2907_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_invert_2911_ = leanh::lean_ctor_get_uint8(
                        v_rhs_2905_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_invert_2911_ == 0 {
                        v_gate_2912_ = leanh::lean_ctor_get(v_rhs_2905_, 0);
                        leanh::lean_inc(v_gate_2912_);
                        leanh::lean_dec_ref(v_rhs_2905_);
                        v___y_2899_ = v_gate_2912_;
                        v___y_2900_ = v___y_2907_;
                        state = 2;
                        continue;
                    } else {
                        v_gate_2913_ = leanh::lean_ctor_get(v_rhs_2905_, 0);
                        leanh::lean_inc(v_gate_2913_);
                        leanh::lean_dec_ref(v_rhs_2905_);
                        v___y_2893_ = v_gate_2913_;
                        v___y_2894_ = v___y_2907_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                if v_linv_2890_ == 0 {
                    if v_invert_2915_ == 0 {
                        leanh::lean_del_object(v___x_2917_);
                        state = 7;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                } else {
                    if v_invert_2915_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2917_);
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2920_ = 1;
                if v_isShared_2918_ == 0 {
                    v___x_2922_ = v___x_2917_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2923_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_gate_2914_);
                    v___x_2922_ = v_reuseFailAlloc_2923_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2922_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2920_,
                );
                v___y_2907_ = v___x_2922_;
                state = 3;
                continue;
            }
            7 => {
                v___x_2925_ = 0;
                v___x_2926_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2926_, 0, v_gate_2914_);
                leanh::lean_ctor_set_uint8(
                    v___x_2926_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2925_,
                );
                v___y_2907_ = v___x_2926_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_BinaryInput_invert___redArg___boxed(
    mut v_input_2928_: *mut leanh::LeanObject,
    mut v_linv_2929_: *mut leanh::LeanObject,
    mut v_rinv_2930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_linv_boxed_2931_: u8 = 0;
    let mut v_rinv_boxed_2932_: u8 = 0;
    let mut v_res_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_linv_boxed_2931_ = (leanh::lean_unbox(v_linv_2929_) as u8);
    v_rinv_boxed_2932_ = (leanh::lean_unbox(v_rinv_2930_) as u8);
    v_res_2933_ = l_Std_Sat_AIG_BinaryInput_invert___redArg(
        v_input_2928_,
        v_linv_boxed_2931_,
        v_rinv_boxed_2932_,
    );
    return v_res_2933_;
}
pub unsafe fn l_Std_Sat_AIG_BinaryInput_invert(
    mut v_00_u03b1_2934_: *mut leanh::LeanObject,
    mut v_inst_2935_: *mut leanh::LeanObject,
    mut v_inst_2936_: *mut leanh::LeanObject,
    mut v_aig_2937_: *mut leanh::LeanObject,
    mut v_input_2938_: *mut leanh::LeanObject,
    mut v_linv_2939_: u8,
    mut v_rinv_2940_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u8 = 0;
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: u8 = 0;
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2957_: u8 = 0;
    let mut v_gate_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2960_: u8 = 0;
    let mut v_gate_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2964_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2967_: u8 = 0;
    let mut v___x_2969_: u8 = 0;
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_2953_ = leanh::lean_ctor_get(v_input_2938_, 0);
                leanh::lean_inc_ref(v_lhs_2953_);
                v_rhs_2954_ = leanh::lean_ctor_get(v_input_2938_, 1);
                leanh::lean_inc_ref(v_rhs_2954_);
                leanh::lean_dec_ref(v_input_2938_);
                v_gate_2963_ = leanh::lean_ctor_get(v_lhs_2953_, 0);
                v_invert_2964_ = leanh::lean_ctor_get_uint8(
                    v_lhs_2953_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_2976_ = (!leanh::lean_is_exclusive(v_lhs_2953_)) as u8;
                if v_isSharedCheck_2976_ == 0 {
                    v___x_2966_ = v_lhs_2953_;
                    v_isShared_2967_ = v_isSharedCheck_2976_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2963_);
                    leanh::lean_dec(v_lhs_2953_);
                    v___x_2966_ = leanh::lean_box(0);
                    v_isShared_2967_ = v_isSharedCheck_2976_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_2944_ = 0;
                v___x_2945_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2945_, 0, v___y_2942_);
                leanh::lean_ctor_set_uint8(
                    v___x_2945_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2944_,
                );
                v___x_2946_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2946_, 0, v___y_2943_);
                leanh::lean_ctor_set(v___x_2946_, 1, v___x_2945_);
                return v___x_2946_;
            }
            2 => {
                v___x_2950_ = 1;
                v___x_2951_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2951_, 0, v___y_2948_);
                leanh::lean_ctor_set_uint8(
                    v___x_2951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2950_,
                );
                v___x_2952_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2952_, 0, v___y_2949_);
                leanh::lean_ctor_set(v___x_2952_, 1, v___x_2951_);
                return v___x_2952_;
            }
            3 => {
                if v_rinv_2940_ == 0 {
                    v_invert_2957_ = leanh::lean_ctor_get_uint8(
                        v_rhs_2954_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_invert_2957_ == 0 {
                        v_gate_2958_ = leanh::lean_ctor_get(v_rhs_2954_, 0);
                        leanh::lean_inc(v_gate_2958_);
                        leanh::lean_dec_ref(v_rhs_2954_);
                        v___y_2942_ = v_gate_2958_;
                        v___y_2943_ = v___y_2956_;
                        state = 1;
                        continue;
                    } else {
                        v_gate_2959_ = leanh::lean_ctor_get(v_rhs_2954_, 0);
                        leanh::lean_inc(v_gate_2959_);
                        leanh::lean_dec_ref(v_rhs_2954_);
                        v___y_2948_ = v_gate_2959_;
                        v___y_2949_ = v___y_2956_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_invert_2960_ = leanh::lean_ctor_get_uint8(
                        v_rhs_2954_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_invert_2960_ == 0 {
                        v_gate_2961_ = leanh::lean_ctor_get(v_rhs_2954_, 0);
                        leanh::lean_inc(v_gate_2961_);
                        leanh::lean_dec_ref(v_rhs_2954_);
                        v___y_2948_ = v_gate_2961_;
                        v___y_2949_ = v___y_2956_;
                        state = 2;
                        continue;
                    } else {
                        v_gate_2962_ = leanh::lean_ctor_get(v_rhs_2954_, 0);
                        leanh::lean_inc(v_gate_2962_);
                        leanh::lean_dec_ref(v_rhs_2954_);
                        v___y_2942_ = v_gate_2962_;
                        v___y_2943_ = v___y_2956_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                if v_linv_2939_ == 0 {
                    if v_invert_2964_ == 0 {
                        leanh::lean_del_object(v___x_2966_);
                        state = 7;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                } else {
                    if v_invert_2964_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2966_);
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2969_ = 1;
                if v_isShared_2967_ == 0 {
                    v___x_2971_ = v___x_2966_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_gate_2963_);
                    v___x_2971_ = v_reuseFailAlloc_2972_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2971_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2969_,
                );
                v___y_2956_ = v___x_2971_;
                state = 3;
                continue;
            }
            7 => {
                v___x_2974_ = 0;
                v___x_2975_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2975_, 0, v_gate_2963_);
                leanh::lean_ctor_set_uint8(
                    v___x_2975_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2974_,
                );
                v___y_2956_ = v___x_2975_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_BinaryInput_invert___boxed(
    mut v_00_u03b1_2977_: *mut leanh::LeanObject,
    mut v_inst_2978_: *mut leanh::LeanObject,
    mut v_inst_2979_: *mut leanh::LeanObject,
    mut v_aig_2980_: *mut leanh::LeanObject,
    mut v_input_2981_: *mut leanh::LeanObject,
    mut v_linv_2982_: *mut leanh::LeanObject,
    mut v_rinv_2983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_linv_boxed_2984_: u8 = 0;
    let mut v_rinv_boxed_2985_: u8 = 0;
    let mut v_res_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_linv_boxed_2984_ = (leanh::lean_unbox(v_linv_2982_) as u8);
    v_rinv_boxed_2985_ = (leanh::lean_unbox(v_rinv_2983_) as u8);
    v_res_2986_ = l_Std_Sat_AIG_BinaryInput_invert(
        v_00_u03b1_2977_,
        v_inst_2978_,
        v_inst_2979_,
        v_aig_2980_,
        v_input_2981_,
        v_linv_boxed_2984_,
        v_rinv_boxed_2985_,
    );
    leanh::lean_dec_ref(v_aig_2980_);
    leanh::lean_dec_ref(v_inst_2979_);
    leanh::lean_dec_ref(v_inst_2978_);
    return v_res_2986_;
}
pub unsafe fn l_Std_Sat_AIG_TernaryInput_cast___redArg(
    mut v_input_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_discr_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2993_: u8 = 0;
    let mut v_gate_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_2995_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v_gate_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_3000_: u8 = 0;
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v_gate_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_3005_: u8 = 0;
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_isSharedCheck_3024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_discr_2988_ = leanh::lean_ctor_get(v_input_2987_, 0);
                v_lhs_2989_ = leanh::lean_ctor_get(v_input_2987_, 1);
                v_rhs_2990_ = leanh::lean_ctor_get(v_input_2987_, 2);
                v_isSharedCheck_3024_ = (!leanh::lean_is_exclusive(v_input_2987_)) as u8;
                if v_isSharedCheck_3024_ == 0 {
                    v___x_2992_ = v_input_2987_;
                    v_isShared_2993_ = v_isSharedCheck_3024_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_2990_);
                    leanh::lean_inc(v_lhs_2989_);
                    leanh::lean_inc(v_discr_2988_);
                    leanh::lean_dec(v_input_2987_);
                    v___x_2992_ = leanh::lean_box(0);
                    v_isShared_2993_ = v_isSharedCheck_3024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_2994_ = leanh::lean_ctor_get(v_discr_2988_, 0);
                v_invert_2995_ = leanh::lean_ctor_get_uint8(
                    v_discr_2988_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3023_ = (!leanh::lean_is_exclusive(v_discr_2988_)) as u8;
                if v_isSharedCheck_3023_ == 0 {
                    v___x_2997_ = v_discr_2988_;
                    v_isShared_2998_ = v_isSharedCheck_3023_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2994_);
                    leanh::lean_dec(v_discr_2988_);
                    v___x_2997_ = leanh::lean_box(0);
                    v_isShared_2998_ = v_isSharedCheck_3023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_2999_ = leanh::lean_ctor_get(v_lhs_2989_, 0);
                v_invert_3000_ = leanh::lean_ctor_get_uint8(
                    v_lhs_2989_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3022_ = (!leanh::lean_is_exclusive(v_lhs_2989_)) as u8;
                if v_isSharedCheck_3022_ == 0 {
                    v___x_3002_ = v_lhs_2989_;
                    v_isShared_3003_ = v_isSharedCheck_3022_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_2999_);
                    leanh::lean_dec(v_lhs_2989_);
                    v___x_3002_ = leanh::lean_box(0);
                    v_isShared_3003_ = v_isSharedCheck_3022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_3004_ = leanh::lean_ctor_get(v_rhs_2990_, 0);
                v_invert_3005_ = leanh::lean_ctor_get_uint8(
                    v_rhs_2990_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3021_ = (!leanh::lean_is_exclusive(v_rhs_2990_)) as u8;
                if v_isSharedCheck_3021_ == 0 {
                    v___x_3007_ = v_rhs_2990_;
                    v_isShared_3008_ = v_isSharedCheck_3021_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_3004_);
                    leanh::lean_dec(v_rhs_2990_);
                    v___x_3007_ = leanh::lean_box(0);
                    v_isShared_3008_ = v_isSharedCheck_3021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3008_ == 0 {
                    leanh::lean_ctor_set(v___x_3007_, 0, v_gate_2994_);
                    v___x_3010_ = v___x_3007_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_gate_2994_);
                    v___x_3010_ = v_reuseFailAlloc_3020_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3010_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_2995_,
                );
                if v_isShared_3003_ == 0 {
                    v___x_3012_ = v___x_3002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_gate_2999_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3019_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_3000_,
                    );
                    v___x_3012_ = v_reuseFailAlloc_3019_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2998_ == 0 {
                    leanh::lean_ctor_set(v___x_2997_, 0, v_gate_3004_);
                    v___x_3014_ = v___x_2997_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3018_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_gate_3004_);
                    v___x_3014_ = v_reuseFailAlloc_3018_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3014_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_3005_,
                );
                if v_isShared_2993_ == 0 {
                    leanh::lean_ctor_set(v___x_2992_, 2, v___x_3014_);
                    leanh::lean_ctor_set(v___x_2992_, 1, v___x_3012_);
                    leanh::lean_ctor_set(v___x_2992_, 0, v___x_3010_);
                    v___x_3016_ = v___x_2992_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 2, v___x_3014_);
                    v___x_3016_ = v_reuseFailAlloc_3017_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_TernaryInput_cast(
    mut v_00_u03b1_3025_: *mut leanh::LeanObject,
    mut v_inst_3026_: *mut leanh::LeanObject,
    mut v_inst_3027_: *mut leanh::LeanObject,
    mut v_aig1_3028_: *mut leanh::LeanObject,
    mut v_aig2_3029_: *mut leanh::LeanObject,
    mut v_input_3030_: *mut leanh::LeanObject,
    mut v_h_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_discr_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v_gate_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_3039_: u8 = 0;
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3042_: u8 = 0;
    let mut v_gate_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_3044_: u8 = 0;
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3047_: u8 = 0;
    let mut v_gate_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_3049_: u8 = 0;
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut v_isSharedCheck_3066_: u8 = 0;
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_isSharedCheck_3068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_discr_3032_ = leanh::lean_ctor_get(v_input_3030_, 0);
                v_lhs_3033_ = leanh::lean_ctor_get(v_input_3030_, 1);
                v_rhs_3034_ = leanh::lean_ctor_get(v_input_3030_, 2);
                v_isSharedCheck_3068_ = (!leanh::lean_is_exclusive(v_input_3030_)) as u8;
                if v_isSharedCheck_3068_ == 0 {
                    v___x_3036_ = v_input_3030_;
                    v_isShared_3037_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_3034_);
                    leanh::lean_inc(v_lhs_3033_);
                    leanh::lean_inc(v_discr_3032_);
                    leanh::lean_dec(v_input_3030_);
                    v___x_3036_ = leanh::lean_box(0);
                    v_isShared_3037_ = v_isSharedCheck_3068_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_3038_ = leanh::lean_ctor_get(v_discr_3032_, 0);
                v_invert_3039_ = leanh::lean_ctor_get_uint8(
                    v_discr_3032_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3067_ = (!leanh::lean_is_exclusive(v_discr_3032_)) as u8;
                if v_isSharedCheck_3067_ == 0 {
                    v___x_3041_ = v_discr_3032_;
                    v_isShared_3042_ = v_isSharedCheck_3067_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_3038_);
                    leanh::lean_dec(v_discr_3032_);
                    v___x_3041_ = leanh::lean_box(0);
                    v_isShared_3042_ = v_isSharedCheck_3067_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_3043_ = leanh::lean_ctor_get(v_lhs_3033_, 0);
                v_invert_3044_ = leanh::lean_ctor_get_uint8(
                    v_lhs_3033_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3066_ = (!leanh::lean_is_exclusive(v_lhs_3033_)) as u8;
                if v_isSharedCheck_3066_ == 0 {
                    v___x_3046_ = v_lhs_3033_;
                    v_isShared_3047_ = v_isSharedCheck_3066_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_3043_);
                    leanh::lean_dec(v_lhs_3033_);
                    v___x_3046_ = leanh::lean_box(0);
                    v_isShared_3047_ = v_isSharedCheck_3066_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_3048_ = leanh::lean_ctor_get(v_rhs_3034_, 0);
                v_invert_3049_ = leanh::lean_ctor_get_uint8(
                    v_rhs_3034_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3065_ = (!leanh::lean_is_exclusive(v_rhs_3034_)) as u8;
                if v_isSharedCheck_3065_ == 0 {
                    v___x_3051_ = v_rhs_3034_;
                    v_isShared_3052_ = v_isSharedCheck_3065_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_3048_);
                    leanh::lean_dec(v_rhs_3034_);
                    v___x_3051_ = leanh::lean_box(0);
                    v_isShared_3052_ = v_isSharedCheck_3065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3052_ == 0 {
                    leanh::lean_ctor_set(v___x_3051_, 0, v_gate_3038_);
                    v___x_3054_ = v___x_3051_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3064_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_gate_3038_);
                    v___x_3054_ = v_reuseFailAlloc_3064_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3054_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_3039_,
                );
                if v_isShared_3047_ == 0 {
                    v___x_3056_ = v___x_3046_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3063_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_gate_3043_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3063_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_3044_,
                    );
                    v___x_3056_ = v_reuseFailAlloc_3063_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3042_ == 0 {
                    leanh::lean_ctor_set(v___x_3041_, 0, v_gate_3048_);
                    v___x_3058_ = v___x_3041_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_gate_3048_);
                    v___x_3058_ = v_reuseFailAlloc_3062_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(
                    v___x_3058_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_3049_,
                );
                if v_isShared_3037_ == 0 {
                    leanh::lean_ctor_set(v___x_3036_, 2, v___x_3058_);
                    leanh::lean_ctor_set(v___x_3036_, 1, v___x_3056_);
                    leanh::lean_ctor_set(v___x_3036_, 0, v___x_3054_);
                    v___x_3060_ = v___x_3036_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 2, v___x_3058_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_TernaryInput_cast___boxed(
    mut v_00_u03b1_3069_: *mut leanh::LeanObject,
    mut v_inst_3070_: *mut leanh::LeanObject,
    mut v_inst_3071_: *mut leanh::LeanObject,
    mut v_aig1_3072_: *mut leanh::LeanObject,
    mut v_aig2_3073_: *mut leanh::LeanObject,
    mut v_input_3074_: *mut leanh::LeanObject,
    mut v_h_3075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3076_ = l_Std_Sat_AIG_TernaryInput_cast(
        v_00_u03b1_3069_,
        v_inst_3070_,
        v_inst_3071_,
        v_aig1_3072_,
        v_aig2_3073_,
        v_input_3074_,
        v_h_3075_,
    );
    leanh::lean_dec_ref(v_aig2_3073_);
    leanh::lean_dec_ref(v_aig1_3072_);
    leanh::lean_dec_ref(v_inst_3071_);
    leanh::lean_dec_ref(v_inst_3070_);
    return v_res_3076_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_invEdgeStyle(
    mut v_isInv_3079_: u8,
) -> *mut leanh::LeanObject {
    if v_isInv_3079_ == 0 {
        let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3080_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__0;
        return v___x_3080_;
    } else {
        let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3081_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle___closed__1;
        return v___x_3081_;
    }
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_invEdgeStyle___boxed(
    mut v_isInv_3082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isInv_boxed_3083_: u8 = 0;
    let mut v_res_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isInv_boxed_3083_ = (leanh::lean_unbox(v_isInv_3082_) as u8);
    v_res_3084_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v_isInv_boxed_3083_);
    return v_res_3084_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_go___redArg(
    mut v_acc_3089_: *mut leanh::LeanObject,
    mut v_decls_3090_: *mut leanh::LeanObject,
    mut v_idx_3091_: *mut leanh::LeanObject,
    mut v_a_3092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3107_: u8 = 0;
    let mut v___y_3108_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3132_: u8 = 0;
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: u8 = 0;
    let mut v___x_3137_: u8 = 0;
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3093_ = lean_array_get_size(v_decls_3090_);
                v___x_3094_ = leanh::lean_alloc_closure(
                    l_instDecidableEqFin___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___x_3094_, 0, v___x_3093_);
                v___f_3095_ = leanh::lean_alloc_closure(
                    l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_3095_, 0, v___x_3094_);
                v___f_3096_ = l_Std_Sat_AIG_toGraphviz_go___redArg___closed__0;
                leanh::lean_inc(v_idx_3091_);
                leanh::lean_inc_ref(v___f_3095_);
                v___x_3097_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v___f_3095_,
                    v___f_3096_,
                    v_a_3092_,
                    v_idx_3091_,
                );
                if v___x_3097_ == 0 {
                    v___x_3098_ = leanh::lean_box(0);
                    leanh::lean_inc(v_idx_3091_);
                    v___x_3099_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                        v___f_3095_,
                        v___f_3096_,
                        v_a_3092_,
                        v_idx_3091_,
                        v___x_3098_,
                    );
                    v___x_3100_ = lean_array_fget_borrowed(v_decls_3090_, v_idx_3091_);
                    if leanh::lean_obj_tag(v___x_3100_) == 2 {
                        v_l_3101_ = leanh::lean_ctor_get(v___x_3100_, 0);
                        v_r_3102_ = leanh::lean_ctor_get(v___x_3100_, 1);
                        v___x_3103_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3104_ = lean_nat_shiftr(v_l_3101_, v___x_3103_);
                        v___x_3138_ = lean_nat_land(v___x_3103_, v_l_3101_);
                        v___x_3139_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3140_ = lean_nat_dec_eq(v___x_3138_, v___x_3139_);
                        leanh::lean_dec(v___x_3138_);
                        if v___x_3140_ == 0 {
                            v___x_3141_ = 1;
                            v___y_3132_ = v___x_3141_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3132_ = v___x_3097_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_idx_3091_);
                        v___x_3142_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3142_, 0, v_acc_3089_);
                        leanh::lean_ctor_set(v___x_3142_, 1, v___x_3099_);
                        return v___x_3142_;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_3095_);
                    leanh::lean_dec(v_idx_3091_);
                    v___x_3143_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3143_, 0, v_acc_3089_);
                    leanh::lean_ctor_set(v___x_3143_, 1, v_a_3092_);
                    return v___x_3143_;
                }
            }
            1 => {
                v___x_3109_ = l_Nat_reprFast(v_idx_3091_);
                v___x_3110_ = l_Std_Sat_AIG_toGraphviz_go___redArg___closed__1;
                leanh::lean_inc_ref(v___x_3109_);
                v___x_3111_ = lean_string_append(v___x_3109_, v___x_3110_);
                leanh::lean_inc(v___x_3104_);
                v___x_3112_ = l_Nat_reprFast(v___x_3104_);
                v___x_3113_ = lean_string_append(v___x_3111_, v___x_3112_);
                leanh::lean_dec_ref(v___x_3112_);
                v___x_3114_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_3107_);
                v___x_3115_ = lean_string_append(v___x_3113_, v___x_3114_);
                leanh::lean_dec_ref(v___x_3114_);
                v___x_3116_ = l_Std_Sat_AIG_toGraphviz_go___redArg___closed__2;
                v___x_3117_ = lean_string_append(v___x_3115_, v___x_3116_);
                v___x_3118_ = lean_string_append(v___x_3117_, v___x_3109_);
                leanh::lean_dec_ref(v___x_3109_);
                v___x_3119_ = lean_string_append(v___x_3118_, v___x_3110_);
                leanh::lean_inc(v___y_3106_);
                v___x_3120_ = l_Nat_reprFast(v___y_3106_);
                v___x_3121_ = lean_string_append(v___x_3119_, v___x_3120_);
                leanh::lean_dec_ref(v___x_3120_);
                v___x_3122_ = l_Std_Sat_AIG_toGraphviz_invEdgeStyle(v___y_3108_);
                v___x_3123_ = lean_string_append(v___x_3121_, v___x_3122_);
                leanh::lean_dec_ref(v___x_3122_);
                v___x_3124_ = l_Std_Sat_AIG_toGraphviz_go___redArg___closed__3;
                v___x_3125_ = lean_string_append(v___x_3123_, v___x_3124_);
                v___x_3126_ = lean_string_append(v_acc_3089_, v___x_3125_);
                leanh::lean_dec_ref(v___x_3125_);
                v___x_3127_ = l_Std_Sat_AIG_toGraphviz_go___redArg(
                    v___x_3126_,
                    v_decls_3090_,
                    v___x_3104_,
                    v___x_3099_,
                );
                v_fst_3128_ = leanh::lean_ctor_get(v___x_3127_, 0);
                leanh::lean_inc(v_fst_3128_);
                v_snd_3129_ = leanh::lean_ctor_get(v___x_3127_, 1);
                leanh::lean_inc(v_snd_3129_);
                leanh::lean_dec_ref(v___x_3127_);
                v_acc_3089_ = v_fst_3128_;
                v_idx_3091_ = v___y_3106_;
                v_a_3092_ = v_snd_3129_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3133_ = lean_nat_shiftr(v_r_3102_, v___x_3103_);
                v___x_3134_ = lean_nat_land(v___x_3103_, v_r_3102_);
                v___x_3135_ = leanh::lean_unsigned_to_nat(0);
                v___x_3136_ = lean_nat_dec_eq(v___x_3134_, v___x_3135_);
                leanh::lean_dec(v___x_3134_);
                if v___x_3136_ == 0 {
                    v___x_3137_ = 1;
                    v___y_3106_ = v___x_3133_;
                    v___y_3107_ = v___y_3132_;
                    v___y_3108_ = v___x_3137_;
                    state = 1;
                    continue;
                } else {
                    v___y_3106_ = v___x_3133_;
                    v___y_3107_ = v___y_3132_;
                    v___y_3108_ = v___x_3097_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_go___redArg___boxed(
    mut v_acc_3144_: *mut leanh::LeanObject,
    mut v_decls_3145_: *mut leanh::LeanObject,
    mut v_idx_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ =
        l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_3144_, v_decls_3145_, v_idx_3146_, v_a_3147_);
    leanh::lean_dec_ref(v_decls_3145_);
    return v_res_3148_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_go(
    mut v_00_u03b1_3149_: *mut leanh::LeanObject,
    mut v_inst_3150_: *mut leanh::LeanObject,
    mut v_inst_3151_: *mut leanh::LeanObject,
    mut v_inst_3152_: *mut leanh::LeanObject,
    mut v_acc_3153_: *mut leanh::LeanObject,
    mut v_decls_3154_: *mut leanh::LeanObject,
    mut v_hinv_3155_: *mut leanh::LeanObject,
    mut v_idx_3156_: *mut leanh::LeanObject,
    mut v_hidx_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3159_ =
        l_Std_Sat_AIG_toGraphviz_go___redArg(v_acc_3153_, v_decls_3154_, v_idx_3156_, v_a_3158_);
    return v___x_3159_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_go___boxed(
    mut v_00_u03b1_3160_: *mut leanh::LeanObject,
    mut v_inst_3161_: *mut leanh::LeanObject,
    mut v_inst_3162_: *mut leanh::LeanObject,
    mut v_inst_3163_: *mut leanh::LeanObject,
    mut v_acc_3164_: *mut leanh::LeanObject,
    mut v_decls_3165_: *mut leanh::LeanObject,
    mut v_hinv_3166_: *mut leanh::LeanObject,
    mut v_idx_3167_: *mut leanh::LeanObject,
    mut v_hidx_3168_: *mut leanh::LeanObject,
    mut v_a_3169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Std_Sat_AIG_toGraphviz_go(
        v_00_u03b1_3160_,
        v_inst_3161_,
        v_inst_3162_,
        v_inst_3163_,
        v_acc_3164_,
        v_decls_3165_,
        v_hinv_3166_,
        v_idx_3167_,
        v_hidx_3168_,
        v_a_3169_,
    );
    leanh::lean_dec_ref(v_decls_3165_);
    leanh::lean_dec_ref(v_inst_3163_);
    leanh::lean_dec_ref(v_inst_3162_);
    leanh::lean_dec_ref(v_inst_3161_);
    return v_res_3170_;
}
pub unsafe fn l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(
    mut v_x_3171_: *mut leanh::LeanObject,
    mut v_h__1_3172_: *mut leanh::LeanObject,
    mut v_h__2_3173_: *mut leanh::LeanObject,
    mut v_h__3_3174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3171_) {
        0 => {
            let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3174_);
            leanh::lean_dec(v_h__2_3173_);
            v___x_3175_ = leanh::lean_apply_1(v_h__1_3172_, leanh::lean_box(0));
            return v___x_3175_;
        }
        1 => {
            let mut v_idx_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3174_);
            leanh::lean_dec(v_h__1_3172_);
            v_idx_3176_ = leanh::lean_ctor_get(v_x_3171_, 0);
            leanh::lean_inc(v_idx_3176_);
            leanh::lean_dec_ref_known(v_x_3171_, 1);
            v___x_3177_ =
                leanh::lean_apply_2(v_h__2_3173_, v_idx_3176_, leanh::lean_box(0));
            return v___x_3177_;
        }
        _ => {
            let mut v_l_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_3173_);
            leanh::lean_dec(v_h__1_3172_);
            v_l_3178_ = leanh::lean_ctor_get(v_x_3171_, 0);
            leanh::lean_inc(v_l_3178_);
            v_r_3179_ = leanh::lean_ctor_get(v_x_3171_, 1);
            leanh::lean_inc(v_r_3179_);
            leanh::lean_dec_ref_known(v_x_3171_, 2);
            v___x_3180_ = leanh::lean_apply_3(
                v_h__3_3174_,
                v_l_3178_,
                v_r_3179_,
                leanh::lean_box(0),
            );
            return v___x_3180_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_Basic_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(
    mut v_00_u03b1_3181_: *mut leanh::LeanObject,
    mut v_motive_3182_: *mut leanh::LeanObject,
    mut v_x_3183_: *mut leanh::LeanObject,
    mut v_h__1_3184_: *mut leanh::LeanObject,
    mut v_h__2_3185_: *mut leanh::LeanObject,
    mut v_h__3_3186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3183_) {
        0 => {
            let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3186_);
            leanh::lean_dec(v_h__2_3185_);
            v___x_3187_ = leanh::lean_apply_1(v_h__1_3184_, leanh::lean_box(0));
            return v___x_3187_;
        }
        1 => {
            let mut v_idx_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_3186_);
            leanh::lean_dec(v_h__1_3184_);
            v_idx_3188_ = leanh::lean_ctor_get(v_x_3183_, 0);
            leanh::lean_inc(v_idx_3188_);
            leanh::lean_dec_ref_known(v_x_3183_, 1);
            v___x_3189_ =
                leanh::lean_apply_2(v_h__2_3185_, v_idx_3188_, leanh::lean_box(0));
            return v___x_3189_;
        }
        _ => {
            let mut v_l_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_3185_);
            leanh::lean_dec(v_h__1_3184_);
            v_l_3190_ = leanh::lean_ctor_get(v_x_3183_, 0);
            leanh::lean_inc(v_l_3190_);
            v_r_3191_ = leanh::lean_ctor_get(v_x_3183_, 1);
            leanh::lean_inc(v_r_3191_);
            leanh::lean_dec_ref_known(v_x_3183_, 2);
            v___x_3192_ = leanh::lean_apply_3(
                v_h__3_3186_,
                v_l_3190_,
                v_r_3191_,
                leanh::lean_box(0),
            );
            return v___x_3192_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(
    mut v_inst_3198_: *mut leanh::LeanObject,
    mut v_decls_3199_: *mut leanh::LeanObject,
    mut v_idx_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3201_ = lean_array_fget_borrowed(v_decls_3199_, v_idx_3200_);
    match leanh::lean_obj_tag(v___x_3201_) {
        0 => {
            let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_inst_3198_);
            v___x_3202_ = l_Nat_reprFast(v_idx_3200_);
            v___x_3203_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0;
            v___x_3204_ = lean_string_append(v___x_3202_, v___x_3203_);
            v___x_3205_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__1;
            v___x_3206_ = lean_string_append(v___x_3204_, v___x_3205_);
            v___x_3207_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__2;
            v___x_3208_ = lean_string_append(v___x_3206_, v___x_3207_);
            return v___x_3208_;
        }
        1 => {
            let mut v_idx_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_idx_3209_ = leanh::lean_ctor_get(v___x_3201_, 0);
            v___x_3210_ = l_Nat_reprFast(v_idx_3200_);
            v___x_3211_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0;
            v___x_3212_ = lean_string_append(v___x_3210_, v___x_3211_);
            leanh::lean_inc(v_idx_3209_);
            v___x_3213_ = leanh::lean_apply_1(v_inst_3198_, v_idx_3209_);
            v___x_3214_ = lean_string_append(v___x_3212_, v___x_3213_);
            leanh::lean_dec_ref(v___x_3213_);
            v___x_3215_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__3;
            v___x_3216_ = lean_string_append(v___x_3214_, v___x_3215_);
            return v___x_3216_;
        }
        _ => {
            let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_inst_3198_);
            v___x_3217_ = l_Nat_reprFast(v_idx_3200_);
            v___x_3218_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__0;
            leanh::lean_inc_ref(v___x_3217_);
            v___x_3219_ = lean_string_append(v___x_3217_, v___x_3218_);
            v___x_3220_ = lean_string_append(v___x_3219_, v___x_3217_);
            leanh::lean_dec_ref(v___x_3217_);
            v___x_3221_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___closed__4;
            v___x_3222_ = lean_string_append(v___x_3220_, v___x_3221_);
            return v___x_3222_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg___boxed(
    mut v_inst_3223_: *mut leanh::LeanObject,
    mut v_decls_3224_: *mut leanh::LeanObject,
    mut v_idx_3225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3226_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(
        v_inst_3223_,
        v_decls_3224_,
        v_idx_3225_,
    );
    leanh::lean_dec_ref(v_decls_3224_);
    return v_res_3226_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_toGraphvizString(
    mut v_00_u03b1_3227_: *mut leanh::LeanObject,
    mut v_inst_3228_: *mut leanh::LeanObject,
    mut v_inst_3229_: *mut leanh::LeanObject,
    mut v_inst_3230_: *mut leanh::LeanObject,
    mut v_decls_3231_: *mut leanh::LeanObject,
    mut v_idx_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(
        v_inst_3229_,
        v_decls_3231_,
        v_idx_3232_,
    );
    return v___x_3233_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz_toGraphvizString___boxed(
    mut v_00_u03b1_3234_: *mut leanh::LeanObject,
    mut v_inst_3235_: *mut leanh::LeanObject,
    mut v_inst_3236_: *mut leanh::LeanObject,
    mut v_inst_3237_: *mut leanh::LeanObject,
    mut v_decls_3238_: *mut leanh::LeanObject,
    mut v_idx_3239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Std_Sat_AIG_toGraphviz_toGraphvizString(
        v_00_u03b1_3234_,
        v_inst_3235_,
        v_inst_3236_,
        v_inst_3237_,
        v_decls_3238_,
        v_idx_3239_,
    );
    leanh::lean_dec_ref(v_decls_3238_);
    leanh::lean_dec_ref(v_inst_3237_);
    leanh::lean_dec_ref(v_inst_3235_);
    return v_res_3240_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz___redArg___lam__0(
    mut v_inst_3241_: *mut leanh::LeanObject,
    mut v_decls_3242_: *mut leanh::LeanObject,
    mut v_x1_3243_: *mut leanh::LeanObject,
    mut v_x2_3244_: *mut leanh::LeanObject,
    mut v_x3_3245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ =
        l_Std_Sat_AIG_toGraphviz_toGraphvizString___redArg(v_inst_3241_, v_decls_3242_, v_x2_3244_);
    v___x_3247_ = lean_string_append(v_x1_3243_, v___x_3246_);
    leanh::lean_dec_ref(v___x_3246_);
    return v___x_3247_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed(
    mut v_inst_3248_: *mut leanh::LeanObject,
    mut v_decls_3249_: *mut leanh::LeanObject,
    mut v_x1_3250_: *mut leanh::LeanObject,
    mut v_x2_3251_: *mut leanh::LeanObject,
    mut v_x3_3252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3253_ = l_Std_Sat_AIG_toGraphviz___redArg___lam__0(
        v_inst_3248_,
        v_decls_3249_,
        v_x1_3250_,
        v_x2_3251_,
        v_x3_3252_,
    );
    leanh::lean_dec_ref(v_decls_3249_);
    return v_res_3253_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz___redArg___lam__1(
    mut v___x_3254_: *mut leanh::LeanObject,
    mut v___f_3255_: *mut leanh::LeanObject,
    mut v_acc_3256_: *mut leanh::LeanObject,
    mut v_l_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(
        v___x_3254_,
        v___f_3255_,
        v_acc_3256_,
        v_l_3257_,
    );
    return v___x_3258_;
}
pub unsafe fn _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3260_ = leanh::lean_box(0);
    v___x_3261_ = leanh::lean_unsigned_to_nat(16);
    v___x_3262_ = lean_mk_array(v___x_3261_, v___x_3260_);
    return v___x_3262_;
}
pub unsafe fn _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_toGraphviz___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Std_Sat_AIG_toGraphviz___redArg___closed__1_once),
        _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__1,
    );
    v___x_3264_ = leanh::lean_unsigned_to_nat(0);
    v___x_3265_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3265_, 0, v___x_3264_);
    leanh::lean_ctor_set(v___x_3265_, 1, v___x_3263_);
    return v___x_3265_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz___redArg(
    mut v_inst_3287_: *mut leanh::LeanObject,
    mut v_entry_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_aig_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: u8 = 0;
    let mut v___f_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: u8 = 0;
    let mut v___x_3313_: usize = 0;
    let mut v___x_3314_: usize = 0;
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: usize = 0;
    let mut v___x_3317_: usize = 0;
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_aig_3289_ = leanh::lean_ctor_get(v_entry_3288_, 0);
                leanh::lean_inc_ref(v_aig_3289_);
                v_ref_3290_ = leanh::lean_ctor_get(v_entry_3288_, 1);
                leanh::lean_inc_ref(v_ref_3290_);
                leanh::lean_dec_ref(v_entry_3288_);
                v_decls_3291_ = leanh::lean_ctor_get(v_aig_3289_, 0);
                leanh::lean_inc_ref(v_decls_3291_);
                leanh::lean_dec_ref(v_aig_3289_);
                v_gate_3292_ = leanh::lean_ctor_get(v_ref_3290_, 0);
                leanh::lean_inc(v_gate_3292_);
                leanh::lean_dec_ref(v_ref_3290_);
                v___x_3293_ = l_Std_Sat_AIG_toGraphviz___redArg___closed__0;
                v___x_3294_ = leanh::lean_unsigned_to_nat(0);
                v___x_3295_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Sat_AIG_toGraphviz___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Sat_AIG_toGraphviz___redArg___closed__2_once),
                    _init_l_Std_Sat_AIG_toGraphviz___redArg___closed__2,
                );
                v___x_3296_ = l_Std_Sat_AIG_toGraphviz_go___redArg(
                    v___x_3293_,
                    v_decls_3291_,
                    v_gate_3292_,
                    v___x_3295_,
                );
                v_fst_3297_ = leanh::lean_ctor_get(v___x_3296_, 0);
                leanh::lean_inc(v_fst_3297_);
                v_snd_3298_ = leanh::lean_ctor_get(v___x_3296_, 1);
                leanh::lean_inc(v_snd_3298_);
                leanh::lean_dec_ref(v___x_3296_);
                v___x_3306_ = l_Std_Sat_AIG_toGraphviz___redArg___closed__14;
                v_buckets_3307_ = leanh::lean_ctor_get(v_snd_3298_, 1);
                leanh::lean_inc_ref(v_buckets_3307_);
                leanh::lean_dec(v_snd_3298_);
                v___x_3308_ = lean_array_get_size(v_buckets_3307_);
                v___x_3309_ = lean_nat_dec_lt(v___x_3294_, v___x_3308_);
                if v___x_3309_ == 0 {
                    leanh::lean_dec_ref(v_buckets_3307_);
                    leanh::lean_dec_ref(v_decls_3291_);
                    leanh::lean_dec_ref(v_inst_3287_);
                    v___y_3300_ = v___x_3293_;
                    state = 1;
                    continue;
                } else {
                    v___f_3310_ = leanh::lean_alloc_closure(
                        l_Std_Sat_AIG_toGraphviz___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        5,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3310_, 0, v_inst_3287_);
                    leanh::lean_closure_set(v___f_3310_, 1, v_decls_3291_);
                    v___f_3311_ = leanh::lean_alloc_closure(
                        l_Std_Sat_AIG_toGraphviz___redArg___lam__1 as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3311_, 0, v___x_3306_);
                    leanh::lean_closure_set(v___f_3311_, 1, v___f_3310_);
                    v___x_3312_ = lean_nat_dec_le(v___x_3308_, v___x_3308_);
                    if v___x_3312_ == 0 {
                        if v___x_3309_ == 0 {
                            leanh::lean_dec_ref(v___f_3311_);
                            leanh::lean_dec_ref(v_buckets_3307_);
                            v___y_3300_ = v___x_3293_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3313_ = 0usize;
                            v___x_3314_ = lean_usize_of_nat(v___x_3308_);
                            v___x_3315_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_3306_,
                                    v___f_3311_,
                                    v_buckets_3307_,
                                    v___x_3313_,
                                    v___x_3314_,
                                    v___x_3293_,
                                );
                            v___y_3300_ = v___x_3315_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_3316_ = 0usize;
                        v___x_3317_ = lean_usize_of_nat(v___x_3308_);
                        v___x_3318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_3306_,
                            v___f_3311_,
                            v_buckets_3307_,
                            v___x_3316_,
                            v___x_3317_,
                            v___x_3293_,
                        );
                        v___y_3300_ = v___x_3318_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3301_ = l_Std_Sat_AIG_toGraphviz___redArg___closed__3;
                v___x_3302_ = lean_string_append(v___x_3301_, v___y_3300_);
                leanh::lean_dec_ref(v___y_3300_);
                v___x_3303_ = lean_string_append(v___x_3302_, v_fst_3297_);
                leanh::lean_dec(v_fst_3297_);
                v___x_3304_ = l_Std_Sat_AIG_toGraphviz___redArg___closed__4;
                v___x_3305_ = lean_string_append(v___x_3303_, v___x_3304_);
                return v___x_3305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz(
    mut v_00_u03b1_3319_: *mut leanh::LeanObject,
    mut v_inst_3320_: *mut leanh::LeanObject,
    mut v_inst_3321_: *mut leanh::LeanObject,
    mut v_inst_3322_: *mut leanh::LeanObject,
    mut v_entry_3323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Std_Sat_AIG_toGraphviz___redArg(v_inst_3321_, v_entry_3323_);
    return v___x_3324_;
}
pub unsafe fn l_Std_Sat_AIG_toGraphviz___boxed(
    mut v_00_u03b1_3325_: *mut leanh::LeanObject,
    mut v_inst_3326_: *mut leanh::LeanObject,
    mut v_inst_3327_: *mut leanh::LeanObject,
    mut v_inst_3328_: *mut leanh::LeanObject,
    mut v_entry_3329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3330_ = l_Std_Sat_AIG_toGraphviz(
        v_00_u03b1_3325_,
        v_inst_3326_,
        v_inst_3327_,
        v_inst_3328_,
        v_entry_3329_,
    );
    leanh::lean_dec_ref(v_inst_3328_);
    leanh::lean_dec_ref(v_inst_3326_);
    return v_res_3330_;
}
pub unsafe fn l_Std_Sat_AIG_denote_go___redArg(
    mut v_x_3331_: *mut leanh::LeanObject,
    mut v_decls_3332_: *mut leanh::LeanObject,
    mut v_assign_3333_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3335_: u8 = 0;
    let mut v___y_3336_: u8 = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v_idx_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut v_l_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lval_3347_: u8 = 0;
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rval_3349_: u8 = 0;
    let mut v___y_3351_: u8 = 0;
    let mut v___y_3352_: u8 = 0;
    let mut v___y_3354_: u8 = 0;
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: u8 = 0;
    let mut v___y_3361_: u8 = 0;
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3338_ = lean_array_fget_borrowed(v_decls_3332_, v_x_3331_);
                match leanh::lean_obj_tag(v___x_3338_) {
                    0 => {
                        leanh::lean_dec_ref(v_assign_3333_);
                        v___x_3339_ = 0;
                        return v___x_3339_;
                    }
                    1 => {
                        v_idx_3340_ = leanh::lean_ctor_get(v___x_3338_, 0);
                        leanh::lean_inc(v_idx_3340_);
                        v___x_3341_ = leanh::lean_apply_1(v_assign_3333_, v_idx_3340_);
                        v___x_3342_ = (leanh::lean_unbox(v___x_3341_) as u8);
                        return v___x_3342_;
                    }
                    _ => {
                        v_l_3343_ = leanh::lean_ctor_get(v___x_3338_, 0);
                        v_r_3344_ = leanh::lean_ctor_get(v___x_3338_, 1);
                        v___x_3345_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3346_ = lean_nat_shiftr(v_l_3343_, v___x_3345_);
                        leanh::lean_inc_ref(v_assign_3333_);
                        v_lval_3347_ = l_Std_Sat_AIG_denote_go___redArg(
                            v___x_3346_,
                            v_decls_3332_,
                            v_assign_3333_,
                        );
                        leanh::lean_dec(v___x_3346_);
                        v___x_3348_ = lean_nat_shiftr(v_r_3344_, v___x_3345_);
                        v_rval_3349_ = l_Std_Sat_AIG_denote_go___redArg(
                            v___x_3348_,
                            v_decls_3332_,
                            v_assign_3333_,
                        );
                        leanh::lean_dec(v___x_3348_);
                        v___x_3362_ = lean_nat_land(v___x_3345_, v_l_3343_);
                        v___x_3363_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3364_ = lean_nat_dec_eq(v___x_3362_, v___x_3363_);
                        leanh::lean_dec(v___x_3362_);
                        if v___x_3364_ == 0 {
                            v___x_3365_ = 1;
                            v___y_3361_ = v___x_3365_;
                            state = 4;
                            continue;
                        } else {
                            v___x_3366_ = 0;
                            v___y_3361_ = v___x_3366_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_3336_ == 0 {
                    v___x_3337_ = 1;
                    return v___x_3337_;
                } else {
                    return v___y_3335_;
                }
            }
            2 => {
                if v_rval_3349_ == 0 {
                    if v___y_3352_ == 0 {
                        return v___y_3351_;
                    } else {
                        v___y_3335_ = v___y_3351_;
                        v___y_3336_ = v_rval_3349_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3335_ = v___y_3351_;
                    v___y_3336_ = v___y_3352_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_3354_ == 0 {
                    v___x_3355_ = lean_nat_land(v___x_3345_, v_r_3344_);
                    v___x_3356_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3357_ = lean_nat_dec_eq(v___x_3355_, v___x_3356_);
                    leanh::lean_dec(v___x_3355_);
                    if v___x_3357_ == 0 {
                        v___x_3358_ = 1;
                        v___y_3351_ = v___y_3354_;
                        v___y_3352_ = v___x_3358_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3351_ = v___y_3354_;
                        v___y_3352_ = v___y_3354_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3359_ = 0;
                    return v___x_3359_;
                }
            }
            4 => {
                if v_lval_3347_ == 0 {
                    if v___y_3361_ == 0 {
                        return v___y_3361_;
                    } else {
                        v___y_3354_ = v_lval_3347_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_3354_ = v___y_3361_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_denote_go___redArg___boxed(
    mut v_x_3367_: *mut leanh::LeanObject,
    mut v_decls_3368_: *mut leanh::LeanObject,
    mut v_assign_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3370_: u8 = 0;
    let mut v_r_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3370_ = l_Std_Sat_AIG_denote_go___redArg(v_x_3367_, v_decls_3368_, v_assign_3369_);
    leanh::lean_dec_ref(v_decls_3368_);
    leanh::lean_dec(v_x_3367_);
    v_r_3371_ = leanh::lean_box((v_res_3370_) as usize);
    return v_r_3371_;
}
pub unsafe fn l_Std_Sat_AIG_denote_go(
    mut v_00_u03b1_3372_: *mut leanh::LeanObject,
    mut v_x_3373_: *mut leanh::LeanObject,
    mut v_decls_3374_: *mut leanh::LeanObject,
    mut v_assign_3375_: *mut leanh::LeanObject,
    mut v_h1_3376_: *mut leanh::LeanObject,
    mut v_h2_3377_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3378_: u8 = 0;
    v___x_3378_ = l_Std_Sat_AIG_denote_go___redArg(v_x_3373_, v_decls_3374_, v_assign_3375_);
    return v___x_3378_;
}
pub unsafe fn l_Std_Sat_AIG_denote_go___boxed(
    mut v_00_u03b1_3379_: *mut leanh::LeanObject,
    mut v_x_3380_: *mut leanh::LeanObject,
    mut v_decls_3381_: *mut leanh::LeanObject,
    mut v_assign_3382_: *mut leanh::LeanObject,
    mut v_h1_3383_: *mut leanh::LeanObject,
    mut v_h2_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3385_: u8 = 0;
    let mut v_r_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3385_ = l_Std_Sat_AIG_denote_go(
        v_00_u03b1_3379_,
        v_x_3380_,
        v_decls_3381_,
        v_assign_3382_,
        v_h1_3383_,
        v_h2_3384_,
    );
    leanh::lean_dec_ref(v_decls_3381_);
    leanh::lean_dec(v_x_3380_);
    v_r_3386_ = leanh::lean_box((v_res_3385_) as usize);
    return v_r_3386_;
}
pub unsafe fn l_Std_Sat_AIG_denote___redArg(
    mut v_assign_3387_: *mut leanh::LeanObject,
    mut v_entry_3388_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_3390_: u8 = 0;
    let mut v___x_3391_: u8 = 0;
    let mut v___x_3392_: u8 = 0;
    let mut v_ref_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_3396_: u8 = 0;
    let mut v_decls_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3393_ = leanh::lean_ctor_get(v_entry_3388_, 1);
                v_aig_3394_ = leanh::lean_ctor_get(v_entry_3388_, 0);
                v_gate_3395_ = leanh::lean_ctor_get(v_ref_3393_, 0);
                v_invert_3396_ = leanh::lean_ctor_get_uint8(
                    v_ref_3393_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_decls_3397_ = leanh::lean_ctor_get(v_aig_3394_, 0);
                v___x_3398_ =
                    l_Std_Sat_AIG_denote_go___redArg(v_gate_3395_, v_decls_3397_, v_assign_3387_);
                if v___x_3398_ == 0 {
                    if v_invert_3396_ == 0 {
                        return v_invert_3396_;
                    } else {
                        v___y_3390_ = v___x_3398_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_3390_ = v_invert_3396_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_3390_ == 0 {
                    v___x_3391_ = 1;
                    return v___x_3391_;
                } else {
                    v___x_3392_ = 0;
                    return v___x_3392_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_denote___redArg___boxed(
    mut v_assign_3399_: *mut leanh::LeanObject,
    mut v_entry_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3401_: u8 = 0;
    let mut v_r_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Std_Sat_AIG_denote___redArg(v_assign_3399_, v_entry_3400_);
    leanh::lean_dec_ref(v_entry_3400_);
    v_r_3402_ = leanh::lean_box((v_res_3401_) as usize);
    return v_r_3402_;
}
pub unsafe fn l_Std_Sat_AIG_denote(
    mut v_00_u03b1_3403_: *mut leanh::LeanObject,
    mut v_inst_3404_: *mut leanh::LeanObject,
    mut v_inst_3405_: *mut leanh::LeanObject,
    mut v_assign_3406_: *mut leanh::LeanObject,
    mut v_entry_3407_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3408_: u8 = 0;
    v___x_3408_ = l_Std_Sat_AIG_denote___redArg(v_assign_3406_, v_entry_3407_);
    return v___x_3408_;
}
pub unsafe fn l_Std_Sat_AIG_denote___boxed(
    mut v_00_u03b1_3409_: *mut leanh::LeanObject,
    mut v_inst_3410_: *mut leanh::LeanObject,
    mut v_inst_3411_: *mut leanh::LeanObject,
    mut v_assign_3412_: *mut leanh::LeanObject,
    mut v_entry_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3414_: u8 = 0;
    let mut v_r_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3414_ = l_Std_Sat_AIG_denote(
        v_00_u03b1_3409_,
        v_inst_3410_,
        v_inst_3411_,
        v_assign_3412_,
        v_entry_3413_,
    );
    leanh::lean_dec_ref(v_entry_3413_);
    leanh::lean_dec_ref(v_inst_3411_);
    leanh::lean_dec_ref(v_inst_3410_);
    v_r_3415_ = leanh::lean_box((v_res_3414_) as usize);
    return v_r_3415_;
}
pub unsafe fn _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3497_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__5;
    v___x_3498_ = l_String_toRawSubstring_x27(v___x_3497_);
    return v___x_3498_;
}
pub unsafe fn l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(
    mut v_x_3520_: *mut leanh::LeanObject,
    mut v_a_3521_: *mut leanh::LeanObject,
    mut v_a_3522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: u8 = 0;
    v___x_3523_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
    leanh::lean_inc(v_x_3520_);
    v___x_3524_ = l_Lean_Syntax_isOfKind(v_x_3520_, v___x_3523_);
    if v___x_3524_ == 0 {
        let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3520_);
        v___x_3525_ = leanh::lean_box(1);
        v___x_3526_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3526_, 0, v___x_3525_);
        leanh::lean_ctor_set(v___x_3526_, 1, v_a_3522_);
        return v___x_3526_;
    } else {
        let mut v_quotContext_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3534_: u8 = 0;
        let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_3527_ = leanh::lean_ctor_get(v_a_3521_, 1);
        v_currMacroScope_3528_ = leanh::lean_ctor_get(v_a_3521_, 2);
        v_ref_3529_ = leanh::lean_ctor_get(v_a_3521_, 5);
        v___x_3530_ = leanh::lean_unsigned_to_nat(1);
        v___x_3531_ = l_Lean_Syntax_getArg(v_x_3520_, v___x_3530_);
        v___x_3532_ = leanh::lean_unsigned_to_nat(3);
        v___x_3533_ = l_Lean_Syntax_getArg(v_x_3520_, v___x_3532_);
        leanh::lean_dec(v_x_3520_);
        v___x_3534_ = 0;
        v___x_3535_ = l_Lean_SourceInfo_fromRef(v_ref_3529_, v___x_3534_);
        v___x_3536_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4;
        v___x_3537_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6), core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once), _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
        v___x_3538_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7;
        leanh::lean_inc(v_currMacroScope_3528_);
        leanh::lean_inc(v_quotContext_3527_);
        v___x_3539_ =
            l_Lean_addMacroScope(v_quotContext_3527_, v___x_3538_, v_currMacroScope_3528_);
        v___x_3540_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12;
        leanh::lean_inc_n(v___x_3535_, 2);
        v___x_3541_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_3541_, 0, v___x_3535_);
        leanh::lean_ctor_set(v___x_3541_, 1, v___x_3537_);
        leanh::lean_ctor_set(v___x_3541_, 2, v___x_3539_);
        leanh::lean_ctor_set(v___x_3541_, 3, v___x_3540_);
        v___x_3542_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14;
        v___x_3543_ = l_Lean_Syntax_node2(v___x_3535_, v___x_3542_, v___x_3533_, v___x_3531_);
        v___x_3544_ = l_Lean_Syntax_node2(v___x_3535_, v___x_3536_, v___x_3541_, v___x_3543_);
        v___x_3545_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3545_, 0, v___x_3544_);
        leanh::lean_ctor_set(v___x_3545_, 1, v_a_3522_);
        return v___x_3545_;
    }
}
pub unsafe fn l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___boxed(
    mut v_x_3546_: *mut leanh::LeanObject,
    mut v_a_3547_: *mut leanh::LeanObject,
    mut v_a_3548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3549_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1(v_x_3546_, v_a_3547_, v_a_3548_);
    leanh::lean_dec_ref(v_a_3547_);
    return v_res_3549_;
}
pub unsafe fn _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3566_ = l_Std_Sat_AIG_toGraphviz___redArg___closed__0;
    v___x_3567_ = l_String_toRawSubstring_x27(v___x_3566_);
    return v___x_3567_;
}
pub unsafe fn _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3578_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__11;
    v___x_3579_ = l_String_toRawSubstring_x27(v___x_3578_);
    return v___x_3579_;
}
pub unsafe fn l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(
    mut v_x_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
    mut v_a_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    v___x_3606_ = l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1;
    leanh::lean_inc(v_x_3603_);
    v___x_3607_ = l_Lean_Syntax_isOfKind(v_x_3603_, v___x_3606_);
    if v___x_3607_ == 0 {
        let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3603_);
        v___x_3608_ = leanh::lean_box(1);
        v___x_3609_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3609_, 0, v___x_3608_);
        leanh::lean_ctor_set(v___x_3609_, 1, v_a_3605_);
        return v___x_3609_;
    } else {
        let mut v_quotContext_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_currMacroScope_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ref_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3619_: u8 = 0;
        let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_quotContext_3610_ = leanh::lean_ctor_get(v_a_3604_, 1);
        v_currMacroScope_3611_ = leanh::lean_ctor_get(v_a_3604_, 2);
        v_ref_3612_ = leanh::lean_ctor_get(v_a_3604_, 5);
        v___x_3613_ = leanh::lean_unsigned_to_nat(1);
        v___x_3614_ = l_Lean_Syntax_getArg(v_x_3603_, v___x_3613_);
        v___x_3615_ = leanh::lean_unsigned_to_nat(3);
        v___x_3616_ = l_Lean_Syntax_getArg(v_x_3603_, v___x_3615_);
        v___x_3617_ = leanh::lean_unsigned_to_nat(5);
        v___x_3618_ = l_Lean_Syntax_getArg(v_x_3603_, v___x_3617_);
        leanh::lean_dec(v_x_3603_);
        v___x_3619_ = 0;
        v___x_3620_ = l_Lean_SourceInfo_fromRef(v_ref_3612_, v___x_3619_);
        v___x_3621_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4;
        v___x_3622_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6), core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6_once), _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__6);
        v___x_3623_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__7;
        leanh::lean_inc_n(v_currMacroScope_3611_, 3);
        leanh::lean_inc_n(v_quotContext_3610_, 3);
        v___x_3624_ =
            l_Lean_addMacroScope(v_quotContext_3610_, v___x_3623_, v_currMacroScope_3611_);
        v___x_3625_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__12;
        leanh::lean_inc_n(v___x_3620_, 11);
        v___x_3626_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_3626_, 0, v___x_3620_);
        leanh::lean_ctor_set(v___x_3626_, 1, v___x_3622_);
        leanh::lean_ctor_set(v___x_3626_, 2, v___x_3624_);
        leanh::lean_ctor_set(v___x_3626_, 3, v___x_3625_);
        v___x_3627_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14;
        v___x_3628_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__1;
        v___x_3629_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__3;
        v___x_3630_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__4;
        v___x_3631_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3631_, 0, v___x_3620_);
        leanh::lean_ctor_set(v___x_3631_, 1, v___x_3630_);
        v___x_3632_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__6;
        v___x_3633_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7), core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7_once), _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__7);
        v___x_3634_ = leanh::lean_box(0);
        v___x_3635_ =
            l_Lean_addMacroScope(v_quotContext_3610_, v___x_3634_, v_currMacroScope_3611_);
        v___x_3636_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__10;
        v___x_3637_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_3637_, 0, v___x_3620_);
        leanh::lean_ctor_set(v___x_3637_, 1, v___x_3633_);
        leanh::lean_ctor_set(v___x_3637_, 2, v___x_3635_);
        leanh::lean_ctor_set(v___x_3637_, 3, v___x_3636_);
        v___x_3638_ = l_Lean_Syntax_node1(v___x_3620_, v___x_3632_, v___x_3637_);
        v___x_3639_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3629_, v___x_3631_, v___x_3638_);
        v___x_3640_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12), core::ptr::addr_of_mut!(l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12_once), _init_l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__12);
        v___x_3641_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__15;
        v___x_3642_ =
            l_Lean_addMacroScope(v_quotContext_3610_, v___x_3641_, v_currMacroScope_3611_);
        v___x_3643_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__20;
        v___x_3644_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_3644_, 0, v___x_3620_);
        leanh::lean_ctor_set(v___x_3644_, 1, v___x_3640_);
        leanh::lean_ctor_set(v___x_3644_, 2, v___x_3642_);
        leanh::lean_ctor_set(v___x_3644_, 3, v___x_3643_);
        v___x_3645_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3627_, v___x_3614_, v___x_3616_);
        v___x_3646_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3621_, v___x_3644_, v___x_3645_);
        v___x_3647_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___closed__21;
        v___x_3648_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3648_, 0, v___x_3620_);
        leanh::lean_ctor_set(v___x_3648_, 1, v___x_3647_);
        v___x_3649_ = l_Lean_Syntax_node3(
            v___x_3620_,
            v___x_3628_,
            v___x_3639_,
            v___x_3646_,
            v___x_3648_,
        );
        v___x_3650_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3627_, v___x_3618_, v___x_3649_);
        v___x_3651_ = l_Lean_Syntax_node2(v___x_3620_, v___x_3621_, v___x_3626_, v___x_3650_);
        v___x_3652_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3652_, 0, v___x_3651_);
        leanh::lean_ctor_set(v___x_3652_, 1, v_a_3605_);
        return v___x_3652_;
    }
}
pub unsafe fn l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1___boxed(
    mut v_x_3653_: *mut leanh::LeanObject,
    mut v_a_3654_: *mut leanh::LeanObject,
    mut v_a_3655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3656_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___x2c___u27e7__1(v_x_3653_, v_a_3654_, v_a_3655_);
    leanh::lean_dec_ref(v_a_3654_);
    return v_res_3656_;
}
pub unsafe fn l_Std_Sat_AIG_unexpandDenote(
    mut v_x_3711_: *mut leanh::LeanObject,
    mut v_a_3712_: *mut leanh::LeanObject,
    mut v_a_3713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: u8 = 0;
    v___x_3714_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__4;
    leanh::lean_inc(v_x_3711_);
    v___x_3715_ = l_Lean_Syntax_isOfKind(v_x_3711_, v___x_3714_);
    if v___x_3715_ == 0 {
        let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_3711_);
        v___x_3716_ = leanh::lean_box(0);
        v___x_3717_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3717_, 0, v___x_3716_);
        leanh::lean_ctor_set(v___x_3717_, 1, v_a_3713_);
        return v___x_3717_;
    } else {
        let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3721_: u8 = 0;
        v___x_3718_ = leanh::lean_unsigned_to_nat(1);
        v___x_3719_ = l_Lean_Syntax_getArg(v_x_3711_, v___x_3718_);
        leanh::lean_dec(v_x_3711_);
        v___x_3720_ = leanh::lean_unsigned_to_nat(2);
        leanh::lean_inc(v___x_3719_);
        v___x_3721_ = l_Lean_Syntax_matchesNull(v___x_3719_, v___x_3720_);
        if v___x_3721_ == 0 {
            let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_3719_);
            v___x_3722_ = leanh::lean_box(0);
            v___x_3723_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3723_, 0, v___x_3722_);
            leanh::lean_ctor_set(v___x_3723_, 1, v_a_3713_);
            return v___x_3723_;
        } else {
            let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3727_: u8 = 0;
            v___x_3724_ = leanh::lean_unsigned_to_nat(0);
            v___x_3725_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3724_);
            v___x_3726_ = l_Std_Sat_AIG_unexpandDenote___closed__1;
            leanh::lean_inc(v___x_3725_);
            v___x_3727_ = l_Lean_Syntax_isOfKind(v___x_3725_, v___x_3726_);
            if v___x_3727_ == 0 {
                let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3728_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                leanh::lean_dec(v___x_3719_);
                v___x_3729_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3727_);
                v___x_3730_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                v___x_3731_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                leanh::lean_inc_n(v___x_3729_, 3);
                v___x_3732_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3732_, 0, v___x_3729_);
                leanh::lean_ctor_set(v___x_3732_, 1, v___x_3731_);
                v___x_3733_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                v___x_3734_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3734_, 0, v___x_3729_);
                leanh::lean_ctor_set(v___x_3734_, 1, v___x_3733_);
                v___x_3735_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                v___x_3736_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3736_, 0, v___x_3729_);
                leanh::lean_ctor_set(v___x_3736_, 1, v___x_3735_);
                v___x_3737_ = l_Lean_Syntax_node5(
                    v___x_3729_,
                    v___x_3730_,
                    v___x_3732_,
                    v___x_3725_,
                    v___x_3734_,
                    v___x_3728_,
                    v___x_3736_,
                );
                v___x_3738_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3738_, 0, v___x_3737_);
                leanh::lean_ctor_set(v___x_3738_, 1, v_a_3713_);
                return v___x_3738_;
            } else {
                let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3740_: u8 = 0;
                v___x_3739_ = l_Lean_Syntax_getArg(v___x_3725_, v___x_3718_);
                v___x_3740_ = l_Lean_Syntax_matchesNull(v___x_3739_, v___x_3724_);
                if v___x_3740_ == 0 {
                    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3741_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                    leanh::lean_dec(v___x_3719_);
                    v___x_3742_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3740_);
                    v___x_3743_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                    v___x_3744_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                    leanh::lean_inc_n(v___x_3742_, 3);
                    v___x_3745_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3745_, 0, v___x_3742_);
                    leanh::lean_ctor_set(v___x_3745_, 1, v___x_3744_);
                    v___x_3746_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                    v___x_3747_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3747_, 0, v___x_3742_);
                    leanh::lean_ctor_set(v___x_3747_, 1, v___x_3746_);
                    v___x_3748_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                    v___x_3749_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3749_, 0, v___x_3742_);
                    leanh::lean_ctor_set(v___x_3749_, 1, v___x_3748_);
                    v___x_3750_ = l_Lean_Syntax_node5(
                        v___x_3742_,
                        v___x_3743_,
                        v___x_3745_,
                        v___x_3725_,
                        v___x_3747_,
                        v___x_3741_,
                        v___x_3749_,
                    );
                    v___x_3751_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3751_, 0, v___x_3750_);
                    leanh::lean_ctor_set(v___x_3751_, 1, v_a_3713_);
                    return v___x_3751_;
                } else {
                    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3754_: u8 = 0;
                    v___x_3752_ = l_Lean_Syntax_getArg(v___x_3725_, v___x_3720_);
                    v___x_3753_ = l_Std_Sat_AIG_unexpandDenote___closed__4;
                    leanh::lean_inc(v___x_3752_);
                    v___x_3754_ = l_Lean_Syntax_isOfKind(v___x_3752_, v___x_3753_);
                    if v___x_3754_ == 0 {
                        let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
                        leanh::lean_dec(v___x_3752_);
                        v___x_3755_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                        leanh::lean_dec(v___x_3719_);
                        v___x_3756_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3754_);
                        v___x_3757_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                        v___x_3758_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                        leanh::lean_inc_n(v___x_3756_, 3);
                        v___x_3759_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3759_, 0, v___x_3756_);
                        leanh::lean_ctor_set(v___x_3759_, 1, v___x_3758_);
                        v___x_3760_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                        v___x_3761_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3761_, 0, v___x_3756_);
                        leanh::lean_ctor_set(v___x_3761_, 1, v___x_3760_);
                        v___x_3762_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                        v___x_3763_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3763_, 0, v___x_3756_);
                        leanh::lean_ctor_set(v___x_3763_, 1, v___x_3762_);
                        v___x_3764_ = l_Lean_Syntax_node5(
                            v___x_3756_,
                            v___x_3757_,
                            v___x_3759_,
                            v___x_3725_,
                            v___x_3761_,
                            v___x_3755_,
                            v___x_3763_,
                        );
                        v___x_3765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3765_, 0, v___x_3764_);
                        leanh::lean_ctor_set(v___x_3765_, 1, v_a_3713_);
                        return v___x_3765_;
                    } else {
                        let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3768_: u8 = 0;
                        v___x_3766_ = l_Lean_Syntax_getArg(v___x_3752_, v___x_3724_);
                        leanh::lean_dec(v___x_3752_);
                        v___x_3767_ = leanh::lean_unsigned_to_nat(5);
                        leanh::lean_inc(v___x_3766_);
                        v___x_3768_ = l_Lean_Syntax_matchesNull(v___x_3766_, v___x_3767_);
                        if v___x_3768_ == 0 {
                            let mut v___x_3769_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3770_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3771_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3772_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3773_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3774_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3775_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3776_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3777_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3778_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3779_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_dec(v___x_3766_);
                            v___x_3769_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                            leanh::lean_dec(v___x_3719_);
                            v___x_3770_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3768_);
                            v___x_3771_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                            v___x_3772_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                            leanh::lean_inc_n(v___x_3770_, 3);
                            v___x_3773_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3773_, 0, v___x_3770_);
                            leanh::lean_ctor_set(v___x_3773_, 1, v___x_3772_);
                            v___x_3774_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                            v___x_3775_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3775_, 0, v___x_3770_);
                            leanh::lean_ctor_set(v___x_3775_, 1, v___x_3774_);
                            v___x_3776_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                            v___x_3777_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3777_, 0, v___x_3770_);
                            leanh::lean_ctor_set(v___x_3777_, 1, v___x_3776_);
                            v___x_3778_ = l_Lean_Syntax_node5(
                                v___x_3770_,
                                v___x_3771_,
                                v___x_3773_,
                                v___x_3725_,
                                v___x_3775_,
                                v___x_3769_,
                                v___x_3777_,
                            );
                            v___x_3779_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3779_, 0, v___x_3778_);
                            leanh::lean_ctor_set(v___x_3779_, 1, v_a_3713_);
                            return v___x_3779_;
                        } else {
                            let mut v___x_3780_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3781_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3782_: u8 = 0;
                            v___x_3780_ = l_Lean_Syntax_getArg(v___x_3766_, v___x_3724_);
                            v___x_3781_ = l_Std_Sat_AIG_unexpandDenote___closed__6;
                            leanh::lean_inc(v___x_3780_);
                            v___x_3782_ = l_Lean_Syntax_isOfKind(v___x_3780_, v___x_3781_);
                            if v___x_3782_ == 0 {
                                let mut v___x_3783_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3784_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3785_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3786_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3787_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3788_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3789_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3790_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3791_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3792_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3793_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v___x_3780_);
                                leanh::lean_dec(v___x_3766_);
                                v___x_3783_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                leanh::lean_dec(v___x_3719_);
                                v___x_3784_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3782_);
                                v___x_3785_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                v___x_3786_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                leanh::lean_inc_n(v___x_3784_, 3);
                                v___x_3787_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3787_, 0, v___x_3784_);
                                leanh::lean_ctor_set(v___x_3787_, 1, v___x_3786_);
                                v___x_3788_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                v___x_3789_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3789_, 0, v___x_3784_);
                                leanh::lean_ctor_set(v___x_3789_, 1, v___x_3788_);
                                v___x_3790_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                v___x_3791_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3791_, 0, v___x_3784_);
                                leanh::lean_ctor_set(v___x_3791_, 1, v___x_3790_);
                                v___x_3792_ = l_Lean_Syntax_node5(
                                    v___x_3784_,
                                    v___x_3785_,
                                    v___x_3787_,
                                    v___x_3725_,
                                    v___x_3789_,
                                    v___x_3783_,
                                    v___x_3791_,
                                );
                                v___x_3793_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3793_, 0, v___x_3792_);
                                leanh::lean_ctor_set(v___x_3793_, 1, v_a_3713_);
                                return v___x_3793_;
                            } else {
                                let mut v___x_3794_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3795_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3796_: u8 = 0;
                                v___x_3794_ = l_Lean_Syntax_getArg(v___x_3780_, v___x_3724_);
                                v___x_3795_ = l_Std_Sat_AIG_unexpandDenote___closed__8;
                                leanh::lean_inc(v___x_3794_);
                                v___x_3796_ = l_Lean_Syntax_isOfKind(v___x_3794_, v___x_3795_);
                                if v___x_3796_ == 0 {
                                    let mut v___x_3797_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3798_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3799_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3800_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3801_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3802_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3803_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3804_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3805_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3806_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3807_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    leanh::lean_dec(v___x_3794_);
                                    leanh::lean_dec(v___x_3780_);
                                    leanh::lean_dec(v___x_3766_);
                                    v___x_3797_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                    leanh::lean_dec(v___x_3719_);
                                    v___x_3798_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3796_);
                                    v___x_3799_ =
                                        l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                    v___x_3800_ =
                                        l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                    leanh::lean_inc_n(v___x_3798_, 3);
                                    v___x_3801_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3801_, 0, v___x_3798_);
                                    leanh::lean_ctor_set(v___x_3801_, 1, v___x_3800_);
                                    v___x_3802_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                    v___x_3803_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3803_, 0, v___x_3798_);
                                    leanh::lean_ctor_set(v___x_3803_, 1, v___x_3802_);
                                    v___x_3804_ =
                                        l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                    v___x_3805_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3805_, 0, v___x_3798_);
                                    leanh::lean_ctor_set(v___x_3805_, 1, v___x_3804_);
                                    v___x_3806_ = l_Lean_Syntax_node5(
                                        v___x_3798_,
                                        v___x_3799_,
                                        v___x_3801_,
                                        v___x_3725_,
                                        v___x_3803_,
                                        v___x_3797_,
                                        v___x_3805_,
                                    );
                                    v___x_3807_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3807_, 0, v___x_3806_);
                                    leanh::lean_ctor_set(v___x_3807_, 1, v_a_3713_);
                                    return v___x_3807_;
                                } else {
                                    let mut v___x_3808_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3809_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3810_: u8 = 0;
                                    v___x_3808_ = l_Lean_Syntax_getArg(v___x_3794_, v___x_3724_);
                                    v___x_3809_ = l_Std_Sat_AIG_unexpandDenote___closed__10;
                                    v___x_3810_ =
                                        l_Lean_Syntax_matchesIdent(v___x_3808_, v___x_3809_);
                                    leanh::lean_dec(v___x_3808_);
                                    if v___x_3810_ == 0 {
                                        let mut v___x_3811_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3812_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3813_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3814_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3815_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3816_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3817_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3818_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3819_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3820_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3821_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        leanh::lean_dec(v___x_3794_);
                                        leanh::lean_dec(v___x_3780_);
                                        leanh::lean_dec(v___x_3766_);
                                        v___x_3811_ =
                                            l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                        leanh::lean_dec(v___x_3719_);
                                        v___x_3812_ =
                                            l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3810_);
                                        v___x_3813_ =
                                            l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                        v___x_3814_ =
                                            l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                        leanh::lean_inc_n(v___x_3812_, 3);
                                        v___x_3815_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3815_, 0, v___x_3812_);
                                        leanh::lean_ctor_set(v___x_3815_, 1, v___x_3814_);
                                        v___x_3816_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                        v___x_3817_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3817_, 0, v___x_3812_);
                                        leanh::lean_ctor_set(v___x_3817_, 1, v___x_3816_);
                                        v___x_3818_ =
                                            l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                        v___x_3819_ =
                                            leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3819_, 0, v___x_3812_);
                                        leanh::lean_ctor_set(v___x_3819_, 1, v___x_3818_);
                                        v___x_3820_ = l_Lean_Syntax_node5(
                                            v___x_3812_,
                                            v___x_3813_,
                                            v___x_3815_,
                                            v___x_3725_,
                                            v___x_3817_,
                                            v___x_3811_,
                                            v___x_3819_,
                                        );
                                        v___x_3821_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3821_, 0, v___x_3820_);
                                        leanh::lean_ctor_set(v___x_3821_, 1, v_a_3713_);
                                        return v___x_3821_;
                                    } else {
                                        let mut v___x_3822_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_3823_: u8 = 0;
                                        v___x_3822_ =
                                            l_Lean_Syntax_getArg(v___x_3794_, v___x_3718_);
                                        leanh::lean_dec(v___x_3794_);
                                        v___x_3823_ =
                                            l_Lean_Syntax_matchesNull(v___x_3822_, v___x_3724_);
                                        if v___x_3823_ == 0 {
                                            let mut v___x_3824_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3825_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3826_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3827_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3828_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3829_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3830_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3831_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3832_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3833_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3834_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            leanh::lean_dec(v___x_3780_);
                                            leanh::lean_dec(v___x_3766_);
                                            v___x_3824_ =
                                                l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                            leanh::lean_dec(v___x_3719_);
                                            v___x_3825_ =
                                                l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3823_);
                                            v___x_3826_ =
                                                l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                            v___x_3827_ =
                                                l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                            leanh::lean_inc_n(v___x_3825_, 3);
                                            v___x_3828_ =
                                                leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3828_,
                                                0,
                                                v___x_3825_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3828_,
                                                1,
                                                v___x_3827_,
                                            );
                                            v___x_3829_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                            v___x_3830_ =
                                                leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3830_,
                                                0,
                                                v___x_3825_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3830_,
                                                1,
                                                v___x_3829_,
                                            );
                                            v___x_3831_ =
                                                l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                            v___x_3832_ =
                                                leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3832_,
                                                0,
                                                v___x_3825_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_3832_,
                                                1,
                                                v___x_3831_,
                                            );
                                            v___x_3833_ = l_Lean_Syntax_node5(
                                                v___x_3825_,
                                                v___x_3826_,
                                                v___x_3828_,
                                                v___x_3725_,
                                                v___x_3830_,
                                                v___x_3824_,
                                                v___x_3832_,
                                            );
                                            v___x_3834_ =
                                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3834_,
                                                0,
                                                v___x_3833_,
                                            );
                                            leanh::lean_ctor_set(v___x_3834_, 1, v_a_3713_);
                                            return v___x_3834_;
                                        } else {
                                            let mut v___x_3835_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3836_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_3837_: u8 = 0;
                                            v___x_3835_ =
                                                l_Lean_Syntax_getArg(v___x_3780_, v___x_3718_);
                                            leanh::lean_dec(v___x_3780_);
                                            v___x_3836_ = leanh::lean_unsigned_to_nat(3);
                                            leanh::lean_inc(v___x_3835_);
                                            v___x_3837_ =
                                                l_Lean_Syntax_matchesNull(v___x_3835_, v___x_3836_);
                                            if v___x_3837_ == 0 {
                                                let mut v___x_3838_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3839_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3840_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3841_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3842_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3843_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3844_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3845_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3846_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3847_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3848_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                leanh::lean_dec(v___x_3835_);
                                                leanh::lean_dec(v___x_3766_);
                                                v___x_3838_ =
                                                    l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                                leanh::lean_dec(v___x_3719_);
                                                v___x_3839_ = l_Lean_SourceInfo_fromRef(
                                                    v_a_3712_,
                                                    v___x_3837_,
                                                );
                                                v___x_3840_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                v___x_3841_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                leanh::lean_inc_n(v___x_3839_, 3);
                                                v___x_3842_ =
                                                    leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3842_,
                                                    0,
                                                    v___x_3839_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3842_,
                                                    1,
                                                    v___x_3841_,
                                                );
                                                v___x_3843_ =
                                                    l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                v___x_3844_ =
                                                    leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3844_,
                                                    0,
                                                    v___x_3839_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3844_,
                                                    1,
                                                    v___x_3843_,
                                                );
                                                v___x_3845_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                v___x_3846_ =
                                                    leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3846_,
                                                    0,
                                                    v___x_3839_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3846_,
                                                    1,
                                                    v___x_3845_,
                                                );
                                                v___x_3847_ = l_Lean_Syntax_node5(
                                                    v___x_3839_,
                                                    v___x_3840_,
                                                    v___x_3842_,
                                                    v___x_3725_,
                                                    v___x_3844_,
                                                    v___x_3838_,
                                                    v___x_3846_,
                                                );
                                                v___x_3848_ =
                                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3848_,
                                                    0,
                                                    v___x_3847_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3848_,
                                                    1,
                                                    v_a_3713_,
                                                );
                                                return v___x_3848_;
                                            } else {
                                                let mut v___x_3849_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_3850_: u8 = 0;
                                                v___x_3849_ =
                                                    l_Lean_Syntax_getArg(v___x_3835_, v___x_3724_);
                                                v___x_3850_ = l_Lean_Syntax_matchesNull(
                                                    v___x_3849_,
                                                    v___x_3724_,
                                                );
                                                if v___x_3850_ == 0 {
                                                    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    leanh::lean_dec(v___x_3835_);
                                                    leanh::lean_dec(v___x_3766_);
                                                    v___x_3851_ = l_Lean_Syntax_getArg(
                                                        v___x_3719_,
                                                        v___x_3718_,
                                                    );
                                                    leanh::lean_dec(v___x_3719_);
                                                    v___x_3852_ = l_Lean_SourceInfo_fromRef(
                                                        v_a_3712_,
                                                        v___x_3850_,
                                                    );
                                                    v___x_3853_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                    v___x_3854_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                    leanh::lean_inc_n(v___x_3852_, 3);
                                                    v___x_3855_ = leanh::lean_alloc_ctor(
                                                        2,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3855_,
                                                        0,
                                                        v___x_3852_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3855_,
                                                        1,
                                                        v___x_3854_,
                                                    );
                                                    v___x_3856_ =
                                                        l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                    v___x_3857_ = leanh::lean_alloc_ctor(
                                                        2,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3857_,
                                                        0,
                                                        v___x_3852_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3857_,
                                                        1,
                                                        v___x_3856_,
                                                    );
                                                    v___x_3858_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                    v___x_3859_ = leanh::lean_alloc_ctor(
                                                        2,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3859_,
                                                        0,
                                                        v___x_3852_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3859_,
                                                        1,
                                                        v___x_3858_,
                                                    );
                                                    v___x_3860_ = l_Lean_Syntax_node5(
                                                        v___x_3852_,
                                                        v___x_3853_,
                                                        v___x_3855_,
                                                        v___x_3725_,
                                                        v___x_3857_,
                                                        v___x_3851_,
                                                        v___x_3859_,
                                                    );
                                                    v___x_3861_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        2,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3861_,
                                                        0,
                                                        v___x_3860_,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3861_,
                                                        1,
                                                        v_a_3713_,
                                                    );
                                                    return v___x_3861_;
                                                } else {
                                                    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_3863_: u8 = 0;
                                                    v___x_3862_ = l_Lean_Syntax_getArg(
                                                        v___x_3835_,
                                                        v___x_3718_,
                                                    );
                                                    v___x_3863_ = l_Lean_Syntax_matchesNull(
                                                        v___x_3862_,
                                                        v___x_3724_,
                                                    );
                                                    if v___x_3863_ == 0 {
                                                        let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        leanh::lean_dec(v___x_3835_);
                                                        leanh::lean_dec(v___x_3766_);
                                                        v___x_3864_ = l_Lean_Syntax_getArg(
                                                            v___x_3719_,
                                                            v___x_3718_,
                                                        );
                                                        leanh::lean_dec(v___x_3719_);
                                                        v___x_3865_ = l_Lean_SourceInfo_fromRef(
                                                            v_a_3712_,
                                                            v___x_3863_,
                                                        );
                                                        v___x_3866_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                        v___x_3867_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                        leanh::lean_inc_n(v___x_3865_, 3);
                                                        v___x_3868_ = leanh::lean_alloc_ctor(
                                                            2,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3868_,
                                                            0,
                                                            v___x_3865_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3868_,
                                                            1,
                                                            v___x_3867_,
                                                        );
                                                        v___x_3869_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                        v___x_3870_ = leanh::lean_alloc_ctor(
                                                            2,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3870_,
                                                            0,
                                                            v___x_3865_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3870_,
                                                            1,
                                                            v___x_3869_,
                                                        );
                                                        v___x_3871_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                        v___x_3872_ = leanh::lean_alloc_ctor(
                                                            2,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3872_,
                                                            0,
                                                            v___x_3865_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3872_,
                                                            1,
                                                            v___x_3871_,
                                                        );
                                                        v___x_3873_ = l_Lean_Syntax_node5(
                                                            v___x_3865_,
                                                            v___x_3866_,
                                                            v___x_3868_,
                                                            v___x_3725_,
                                                            v___x_3870_,
                                                            v___x_3864_,
                                                            v___x_3872_,
                                                        );
                                                        v___x_3874_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3874_,
                                                            0,
                                                            v___x_3873_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3874_,
                                                            1,
                                                            v_a_3713_,
                                                        );
                                                        return v___x_3874_;
                                                    } else {
                                                        let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_3877_: u8 = 0;
                                                        v___x_3875_ = l_Lean_Syntax_getArg(
                                                            v___x_3835_,
                                                            v___x_3720_,
                                                        );
                                                        leanh::lean_dec(v___x_3835_);
                                                        v___x_3876_ = l_Std_Sat_AIG_unexpandDenote___closed__12;
                                                        leanh::lean_inc(v___x_3875_);
                                                        v___x_3877_ = l_Lean_Syntax_isOfKind(
                                                            v___x_3875_,
                                                            v___x_3876_,
                                                        );
                                                        if v___x_3877_ == 0 {
                                                            let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            leanh::lean_dec(v___x_3875_);
                                                            leanh::lean_dec(v___x_3766_);
                                                            v___x_3878_ = l_Lean_Syntax_getArg(
                                                                v___x_3719_,
                                                                v___x_3718_,
                                                            );
                                                            leanh::lean_dec(v___x_3719_);
                                                            v___x_3879_ = l_Lean_SourceInfo_fromRef(
                                                                v_a_3712_,
                                                                v___x_3877_,
                                                            );
                                                            v___x_3880_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                            v___x_3881_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                            leanh::lean_inc_n(
                                                                v___x_3879_,
                                                                3,
                                                            );
                                                            v___x_3882_ =
                                                                leanh::lean_alloc_ctor(
                                                                    2,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3882_,
                                                                0,
                                                                v___x_3879_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_3882_,
                                                                1,
                                                                v___x_3881_,
                                                            );
                                                            v___x_3883_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                            v___x_3884_ =
                                                                leanh::lean_alloc_ctor(
                                                                    2,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3884_,
                                                                0,
                                                                v___x_3879_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_3884_,
                                                                1,
                                                                v___x_3883_,
                                                            );
                                                            v___x_3885_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                            v___x_3886_ =
                                                                leanh::lean_alloc_ctor(
                                                                    2,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3886_,
                                                                0,
                                                                v___x_3879_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_3886_,
                                                                1,
                                                                v___x_3885_,
                                                            );
                                                            v___x_3887_ = l_Lean_Syntax_node5(
                                                                v___x_3879_,
                                                                v___x_3880_,
                                                                v___x_3882_,
                                                                v___x_3725_,
                                                                v___x_3884_,
                                                                v___x_3878_,
                                                                v___x_3886_,
                                                            );
                                                            v___x_3888_ =
                                                                leanh::lean_alloc_ctor(
                                                                    0,
                                                                    2,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3888_,
                                                                0,
                                                                v___x_3887_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_3888_,
                                                                1,
                                                                v_a_3713_,
                                                            );
                                                            return v___x_3888_;
                                                        } else {
                                                            let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_3890_: u8 = 0;
                                                            v___x_3889_ = l_Lean_Syntax_getArg(
                                                                v___x_3875_,
                                                                v___x_3718_,
                                                            );
                                                            v___x_3890_ = l_Lean_Syntax_matchesNull(
                                                                v___x_3889_,
                                                                v___x_3724_,
                                                            );
                                                            if v___x_3890_ == 0 {
                                                                let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                leanh::lean_dec(v___x_3875_);
                                                                leanh::lean_dec(v___x_3766_);
                                                                v___x_3891_ = l_Lean_Syntax_getArg(
                                                                    v___x_3719_,
                                                                    v___x_3718_,
                                                                );
                                                                leanh::lean_dec(v___x_3719_);
                                                                v___x_3892_ =
                                                                    l_Lean_SourceInfo_fromRef(
                                                                        v_a_3712_,
                                                                        v___x_3890_,
                                                                    );
                                                                v___x_3893_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                                v___x_3894_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                                leanh::lean_inc_n(
                                                                    v___x_3892_,
                                                                    3,
                                                                );
                                                                v___x_3895_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        2,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3895_,
                                                                    0,
                                                                    v___x_3892_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3895_,
                                                                    1,
                                                                    v___x_3894_,
                                                                );
                                                                v___x_3896_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                                v___x_3897_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        2,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3897_,
                                                                    0,
                                                                    v___x_3892_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3897_,
                                                                    1,
                                                                    v___x_3896_,
                                                                );
                                                                v___x_3898_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                                v___x_3899_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        2,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3899_,
                                                                    0,
                                                                    v___x_3892_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3899_,
                                                                    1,
                                                                    v___x_3898_,
                                                                );
                                                                v___x_3900_ = l_Lean_Syntax_node5(
                                                                    v___x_3892_,
                                                                    v___x_3893_,
                                                                    v___x_3895_,
                                                                    v___x_3725_,
                                                                    v___x_3897_,
                                                                    v___x_3891_,
                                                                    v___x_3899_,
                                                                );
                                                                v___x_3901_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        2,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3901_,
                                                                    0,
                                                                    v___x_3900_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3901_,
                                                                    1,
                                                                    v_a_3713_,
                                                                );
                                                                return v___x_3901_;
                                                            } else {
                                                                let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_3903_: u8 = 0;
                                                                v___x_3902_ = l_Lean_Syntax_getArg(
                                                                    v___x_3766_,
                                                                    v___x_3720_,
                                                                );
                                                                leanh::lean_inc(v___x_3902_);
                                                                v___x_3903_ =
                                                                    l_Lean_Syntax_isOfKind(
                                                                        v___x_3902_,
                                                                        v___x_3781_,
                                                                    );
                                                                if v___x_3903_ == 0 {
                                                                    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    leanh::lean_dec(
                                                                        v___x_3902_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3875_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3766_,
                                                                    );
                                                                    v___x_3904_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v___x_3719_,
                                                                            v___x_3718_,
                                                                        );
                                                                    leanh::lean_dec(
                                                                        v___x_3719_,
                                                                    );
                                                                    v___x_3905_ =
                                                                        l_Lean_SourceInfo_fromRef(
                                                                            v_a_3712_,
                                                                            v___x_3903_,
                                                                        );
                                                                    v___x_3906_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                                    v___x_3907_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                                    leanh::lean_inc_n(
                                                                        v___x_3905_,
                                                                        3,
                                                                    );
                                                                    v___x_3908_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3908_,
                                                                        0,
                                                                        v___x_3905_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3908_,
                                                                        1,
                                                                        v___x_3907_,
                                                                    );
                                                                    v___x_3909_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                                    v___x_3910_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3910_,
                                                                        0,
                                                                        v___x_3905_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3910_,
                                                                        1,
                                                                        v___x_3909_,
                                                                    );
                                                                    v___x_3911_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                                    v___x_3912_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3912_,
                                                                        0,
                                                                        v___x_3905_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3912_,
                                                                        1,
                                                                        v___x_3911_,
                                                                    );
                                                                    v___x_3913_ =
                                                                        l_Lean_Syntax_node5(
                                                                            v___x_3905_,
                                                                            v___x_3906_,
                                                                            v___x_3908_,
                                                                            v___x_3725_,
                                                                            v___x_3910_,
                                                                            v___x_3904_,
                                                                            v___x_3912_,
                                                                        );
                                                                    v___x_3914_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3914_,
                                                                        0,
                                                                        v___x_3913_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3914_,
                                                                        1,
                                                                        v_a_3713_,
                                                                    );
                                                                    return v___x_3914_;
                                                                } else {
                                                                    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                    let mut v___x_3916_: u8 = 0;
                                                                    v___x_3915_ =
                                                                        l_Lean_Syntax_getArg(
                                                                            v___x_3902_,
                                                                            v___x_3724_,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v___x_3915_,
                                                                    );
                                                                    v___x_3916_ =
                                                                        l_Lean_Syntax_isOfKind(
                                                                            v___x_3915_,
                                                                            v___x_3795_,
                                                                        );
                                                                    if v___x_3916_ == 0 {
                                                                        let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        leanh::lean_dec(
                                                                            v___x_3915_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3902_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3875_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3766_,
                                                                        );
                                                                        v___x_3917_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v___x_3719_,
                                                                                v___x_3718_,
                                                                            );
                                                                        leanh::lean_dec(
                                                                            v___x_3719_,
                                                                        );
                                                                        v___x_3918_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3916_);
                                                                        v___x_3919_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                                        v___x_3920_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                                        leanh::lean_inc_n(
                                                                            v___x_3918_,
                                                                            3,
                                                                        );
                                                                        v___x_3921_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3921_,
                                                                            0,
                                                                            v___x_3918_,
                                                                        );
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3921_,
                                                                            1,
                                                                            v___x_3920_,
                                                                        );
                                                                        v___x_3922_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                                        v___x_3923_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3923_,
                                                                            0,
                                                                            v___x_3918_,
                                                                        );
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3923_,
                                                                            1,
                                                                            v___x_3922_,
                                                                        );
                                                                        v___x_3924_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                                        v___x_3925_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3925_,
                                                                            0,
                                                                            v___x_3918_,
                                                                        );
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3925_,
                                                                            1,
                                                                            v___x_3924_,
                                                                        );
                                                                        v___x_3926_ =
                                                                            l_Lean_Syntax_node5(
                                                                                v___x_3918_,
                                                                                v___x_3919_,
                                                                                v___x_3921_,
                                                                                v___x_3725_,
                                                                                v___x_3923_,
                                                                                v___x_3917_,
                                                                                v___x_3925_,
                                                                            );
                                                                        v___x_3927_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3927_,
                                                                            0,
                                                                            v___x_3926_,
                                                                        );
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3927_,
                                                                            1,
                                                                            v_a_3713_,
                                                                        );
                                                                        return v___x_3927_;
                                                                    } else {
                                                                        let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                        let mut v___x_3930_: u8 = 0;
                                                                        v___x_3928_ =
                                                                            l_Lean_Syntax_getArg(
                                                                                v___x_3915_,
                                                                                v___x_3724_,
                                                                            );
                                                                        v___x_3929_ = l_Std_Sat_AIG_unexpandDenote___closed__14;
                                                                        v___x_3930_ = l_Lean_Syntax_matchesIdent(v___x_3928_, v___x_3929_);
                                                                        leanh::lean_dec(
                                                                            v___x_3928_,
                                                                        );
                                                                        if v___x_3930_ == 0 {
                                                                            let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            leanh::lean_dec(
                                                                                v___x_3915_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3902_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3875_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3766_,
                                                                            );
                                                                            v___x_3931_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                                                            leanh::lean_dec(
                                                                                v___x_3719_,
                                                                            );
                                                                            v___x_3932_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3930_);
                                                                            v___x_3933_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                                            v___x_3934_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                                            leanh::lean_inc_n(v___x_3932_, 3);
                                                                            v___x_3935_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                            leanh::lean_ctor_set(v___x_3935_, 0, v___x_3932_);
                                                                            leanh::lean_ctor_set(v___x_3935_, 1, v___x_3934_);
                                                                            v___x_3936_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                                            v___x_3937_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                            leanh::lean_ctor_set(v___x_3937_, 0, v___x_3932_);
                                                                            leanh::lean_ctor_set(v___x_3937_, 1, v___x_3936_);
                                                                            v___x_3938_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                                            v___x_3939_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                            leanh::lean_ctor_set(v___x_3939_, 0, v___x_3932_);
                                                                            leanh::lean_ctor_set(v___x_3939_, 1, v___x_3938_);
                                                                            v___x_3940_ =
                                                                                l_Lean_Syntax_node5(
                                                                                    v___x_3932_,
                                                                                    v___x_3933_,
                                                                                    v___x_3935_,
                                                                                    v___x_3725_,
                                                                                    v___x_3937_,
                                                                                    v___x_3931_,
                                                                                    v___x_3939_,
                                                                                );
                                                                            v___x_3941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                                            leanh::lean_ctor_set(v___x_3941_, 0, v___x_3940_);
                                                                            leanh::lean_ctor_set(v___x_3941_, 1, v_a_3713_);
                                                                            return v___x_3941_;
                                                                        } else {
                                                                            let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                            let mut v___x_3943_: u8 = 0;
                                                                            v___x_3942_ = l_Lean_Syntax_getArg(v___x_3915_, v___x_3718_);
                                                                            leanh::lean_dec(
                                                                                v___x_3915_,
                                                                            );
                                                                            v___x_3943_ = l_Lean_Syntax_matchesNull(v___x_3942_, v___x_3724_);
                                                                            if v___x_3943_ == 0 {
                                                                                let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                leanh::lean_dec(v___x_3902_);
                                                                                leanh::lean_dec(v___x_3875_);
                                                                                leanh::lean_dec(v___x_3766_);
                                                                                v___x_3944_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                                                                leanh::lean_dec(v___x_3719_);
                                                                                v___x_3945_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3943_);
                                                                                v___x_3946_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                                                v___x_3947_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                                                leanh::lean_inc_n(v___x_3945_, 3);
                                                                                v___x_3948_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                leanh::lean_ctor_set(v___x_3948_, 0, v___x_3945_);
                                                                                leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                                                                                v___x_3949_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                                                v___x_3950_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                leanh::lean_ctor_set(v___x_3950_, 0, v___x_3945_);
                                                                                leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                                                                                v___x_3951_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                                                v___x_3952_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                leanh::lean_ctor_set(v___x_3952_, 0, v___x_3945_);
                                                                                leanh::lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                                                                                v___x_3953_ = l_Lean_Syntax_node5(v___x_3945_, v___x_3946_, v___x_3948_, v___x_3725_, v___x_3950_, v___x_3944_, v___x_3952_);
                                                                                v___x_3954_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                                                leanh::lean_ctor_set(v___x_3954_, 0, v___x_3953_);
                                                                                leanh::lean_ctor_set(v___x_3954_, 1, v_a_3713_);
                                                                                return v___x_3954_;
                                                                            } else {
                                                                                let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                let mut v___x_3956_: u8 = 0;
                                                                                v___x_3955_ = l_Lean_Syntax_getArg(v___x_3902_, v___x_3718_);
                                                                                leanh::lean_dec(v___x_3902_);
                                                                                leanh::lean_inc(v___x_3955_);
                                                                                v___x_3956_ = l_Lean_Syntax_matchesNull(v___x_3955_, v___x_3836_);
                                                                                if v___x_3956_ == 0
                                                                                {
                                                                                    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    leanh::lean_dec(v___x_3955_);
                                                                                    leanh::lean_dec(v___x_3875_);
                                                                                    leanh::lean_dec(v___x_3766_);
                                                                                    v___x_3957_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                                                                    leanh::lean_dec(v___x_3719_);
                                                                                    v___x_3958_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3956_);
                                                                                    v___x_3959_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                                                    v___x_3960_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                                                    leanh::lean_inc_n(v___x_3958_, 3);
                                                                                    v___x_3961_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_3958_);
                                                                                    leanh::lean_ctor_set(v___x_3961_, 1, v___x_3960_);
                                                                                    v___x_3962_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                                                    v___x_3963_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                    leanh::lean_ctor_set(v___x_3963_, 0, v___x_3958_);
                                                                                    leanh::lean_ctor_set(v___x_3963_, 1, v___x_3962_);
                                                                                    v___x_3964_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                                                    v___x_3965_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                    leanh::lean_ctor_set(v___x_3965_, 0, v___x_3958_);
                                                                                    leanh::lean_ctor_set(v___x_3965_, 1, v___x_3964_);
                                                                                    v___x_3966_ = l_Lean_Syntax_node5(v___x_3958_, v___x_3959_, v___x_3961_, v___x_3725_, v___x_3963_, v___x_3957_, v___x_3965_);
                                                                                    v___x_3967_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                                                    leanh::lean_ctor_set(v___x_3967_, 0, v___x_3966_);
                                                                                    leanh::lean_ctor_set(v___x_3967_, 1, v_a_3713_);
                                                                                    return v___x_3967_;
                                                                                } else {
                                                                                    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                    let mut v___x_3969_: u8 = 0;
                                                                                    v___x_3968_ = l_Lean_Syntax_getArg(v___x_3955_, v___x_3724_);
                                                                                    v___x_3969_ = l_Lean_Syntax_matchesNull(v___x_3968_, v___x_3724_);
                                                                                    if v___x_3969_
                                                                                        == 0
                                                                                    {
                                                                                        let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        leanh::lean_dec(v___x_3955_);
                                                                                        leanh::lean_dec(v___x_3875_);
                                                                                        leanh::lean_dec(v___x_3766_);
                                                                                        v___x_3970_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
                                                                                        leanh::lean_dec(v___x_3719_);
                                                                                        v___x_3971_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3969_);
                                                                                        v___x_3972_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
                                                                                        v___x_3973_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
                                                                                        leanh::lean_inc_n(v___x_3971_, 3);
                                                                                        v___x_3974_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                        leanh::lean_ctor_set(v___x_3974_, 0, v___x_3971_);
                                                                                        leanh::lean_ctor_set(v___x_3974_, 1, v___x_3973_);
                                                                                        v___x_3975_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
                                                                                        v___x_3976_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                        leanh::lean_ctor_set(v___x_3976_, 0, v___x_3971_);
                                                                                        leanh::lean_ctor_set(v___x_3976_, 1, v___x_3975_);
                                                                                        v___x_3977_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
                                                                                        v___x_3978_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                                                                        leanh::lean_ctor_set(v___x_3978_, 0, v___x_3971_);
                                                                                        leanh::lean_ctor_set(v___x_3978_, 1, v___x_3977_);
                                                                                        v___x_3979_ = l_Lean_Syntax_node5(v___x_3971_, v___x_3972_, v___x_3974_, v___x_3725_, v___x_3976_, v___x_3970_, v___x_3978_);
                                                                                        v___x_3980_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                                                        leanh::lean_ctor_set(v___x_3980_, 0, v___x_3979_);
                                                                                        leanh::lean_ctor_set(v___x_3980_, 1, v_a_3713_);
                                                                                        return v___x_3980_;
                                                                                    } else {
                                                                                        let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                                        let mut v___x_3982_: u8 = 0;
                                                                                        v___x_3981_ = l_Lean_Syntax_getArg(v___x_3955_, v___x_3718_);
                                                                                        v___x_3982_ = l_Lean_Syntax_matchesNull(v___x_3981_, v___x_3724_);
                                                                                        if v___x_3982_ == 0 {
let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_3955_);
leanh::lean_dec(v___x_3875_);
leanh::lean_dec(v___x_3766_);
v___x_3983_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_3984_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3982_);
v___x_3985_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_3986_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_3984_, 3);
v___x_3987_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_3987_, 0, v___x_3984_);
leanh::lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v___x_3988_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_3989_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_3989_, 0, v___x_3984_);
leanh::lean_ctor_set(v___x_3989_, 1, v___x_3988_);
v___x_3990_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_3991_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_3991_, 0, v___x_3984_);
leanh::lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = l_Lean_Syntax_node5(v___x_3984_, v___x_3985_, v___x_3987_, v___x_3725_, v___x_3989_, v___x_3983_, v___x_3991_);
v___x_3993_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_3993_, 0, v___x_3992_);
leanh::lean_ctor_set(v___x_3993_, 1, v_a_3713_);
return v___x_3993_;
} else {
let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3995_: u8 = 0;
v___x_3994_ = l_Lean_Syntax_getArg(v___x_3955_, v___x_3720_);
leanh::lean_dec(v___x_3955_);
leanh::lean_inc(v___x_3994_);
v___x_3995_ = l_Lean_Syntax_isOfKind(v___x_3994_, v___x_3876_);
if v___x_3995_ == 0 {
let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
leanh::lean_dec(v___x_3766_);
v___x_3996_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_3997_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_3995_);
v___x_3998_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_3999_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_3997_, 3);
v___x_4000_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4000_, 0, v___x_3997_);
leanh::lean_ctor_set(v___x_4000_, 1, v___x_3999_);
v___x_4001_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4002_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4002_, 0, v___x_3997_);
leanh::lean_ctor_set(v___x_4002_, 1, v___x_4001_);
v___x_4003_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4004_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4004_, 0, v___x_3997_);
leanh::lean_ctor_set(v___x_4004_, 1, v___x_4003_);
v___x_4005_ = l_Lean_Syntax_node5(v___x_3997_, v___x_3998_, v___x_4000_, v___x_3725_, v___x_4002_, v___x_3996_, v___x_4004_);
v___x_4006_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4006_, 0, v___x_4005_);
leanh::lean_ctor_set(v___x_4006_, 1, v_a_3713_);
return v___x_4006_;
} else {
let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4008_: u8 = 0;
v___x_4007_ = l_Lean_Syntax_getArg(v___x_3994_, v___x_3718_);
v___x_4008_ = l_Lean_Syntax_matchesNull(v___x_4007_, v___x_3724_);
if v___x_4008_ == 0 {
let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
leanh::lean_dec(v___x_3766_);
v___x_4009_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4010_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4008_);
v___x_4011_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4012_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4010_, 3);
v___x_4013_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4013_, 0, v___x_4010_);
leanh::lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4015_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4015_, 0, v___x_4010_);
leanh::lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4017_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4017_, 0, v___x_4010_);
leanh::lean_ctor_set(v___x_4017_, 1, v___x_4016_);
v___x_4018_ = l_Lean_Syntax_node5(v___x_4010_, v___x_4011_, v___x_4013_, v___x_3725_, v___x_4015_, v___x_4009_, v___x_4017_);
v___x_4019_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4019_, 0, v___x_4018_);
leanh::lean_ctor_set(v___x_4019_, 1, v_a_3713_);
return v___x_4019_;
} else {
let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4022_: u8 = 0;
v___x_4020_ = leanh::lean_unsigned_to_nat(4);
v___x_4021_ = l_Lean_Syntax_getArg(v___x_3766_, v___x_4020_);
leanh::lean_dec(v___x_3766_);
leanh::lean_inc(v___x_4021_);
v___x_4022_ = l_Lean_Syntax_isOfKind(v___x_4021_, v___x_3781_);
if v___x_4022_ == 0 {
let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4021_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4023_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4024_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4022_);
v___x_4025_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4026_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4024_, 3);
v___x_4027_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4027_, 0, v___x_4024_);
leanh::lean_ctor_set(v___x_4027_, 1, v___x_4026_);
v___x_4028_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4029_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4029_, 0, v___x_4024_);
leanh::lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4031_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4031_, 0, v___x_4024_);
leanh::lean_ctor_set(v___x_4031_, 1, v___x_4030_);
v___x_4032_ = l_Lean_Syntax_node5(v___x_4024_, v___x_4025_, v___x_4027_, v___x_3725_, v___x_4029_, v___x_4023_, v___x_4031_);
v___x_4033_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4033_, 0, v___x_4032_);
leanh::lean_ctor_set(v___x_4033_, 1, v_a_3713_);
return v___x_4033_;
} else {
let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4035_: u8 = 0;
v___x_4034_ = l_Lean_Syntax_getArg(v___x_4021_, v___x_3724_);
leanh::lean_inc(v___x_4034_);
v___x_4035_ = l_Lean_Syntax_isOfKind(v___x_4034_, v___x_3795_);
if v___x_4035_ == 0 {
let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4034_);
leanh::lean_dec(v___x_4021_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4036_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4037_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4035_);
v___x_4038_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4039_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4037_, 3);
v___x_4040_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4040_, 0, v___x_4037_);
leanh::lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4042_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4042_, 0, v___x_4037_);
leanh::lean_ctor_set(v___x_4042_, 1, v___x_4041_);
v___x_4043_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4044_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4044_, 0, v___x_4037_);
leanh::lean_ctor_set(v___x_4044_, 1, v___x_4043_);
v___x_4045_ = l_Lean_Syntax_node5(v___x_4037_, v___x_4038_, v___x_4040_, v___x_3725_, v___x_4042_, v___x_4036_, v___x_4044_);
v___x_4046_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4046_, 0, v___x_4045_);
leanh::lean_ctor_set(v___x_4046_, 1, v_a_3713_);
return v___x_4046_;
} else {
let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4049_: u8 = 0;
v___x_4047_ = l_Lean_Syntax_getArg(v___x_4034_, v___x_3724_);
v___x_4048_ = l_Std_Sat_AIG_unexpandDenote___closed__16;
v___x_4049_ = l_Lean_Syntax_matchesIdent(v___x_4047_, v___x_4048_);
leanh::lean_dec(v___x_4047_);
if v___x_4049_ == 0 {
let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4034_);
leanh::lean_dec(v___x_4021_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4050_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4051_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4049_);
v___x_4052_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4053_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4051_, 3);
v___x_4054_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4054_, 0, v___x_4051_);
leanh::lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4056_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4056_, 0, v___x_4051_);
leanh::lean_ctor_set(v___x_4056_, 1, v___x_4055_);
v___x_4057_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4058_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4058_, 0, v___x_4051_);
leanh::lean_ctor_set(v___x_4058_, 1, v___x_4057_);
v___x_4059_ = l_Lean_Syntax_node5(v___x_4051_, v___x_4052_, v___x_4054_, v___x_3725_, v___x_4056_, v___x_4050_, v___x_4058_);
v___x_4060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4060_, 0, v___x_4059_);
leanh::lean_ctor_set(v___x_4060_, 1, v_a_3713_);
return v___x_4060_;
} else {
let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4062_: u8 = 0;
v___x_4061_ = l_Lean_Syntax_getArg(v___x_4034_, v___x_3718_);
leanh::lean_dec(v___x_4034_);
v___x_4062_ = l_Lean_Syntax_matchesNull(v___x_4061_, v___x_3724_);
if v___x_4062_ == 0 {
let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4021_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4063_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4064_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4062_);
v___x_4065_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4066_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4064_, 3);
v___x_4067_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4067_, 0, v___x_4064_);
leanh::lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4069_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4069_, 0, v___x_4064_);
leanh::lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4071_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4071_, 0, v___x_4064_);
leanh::lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = l_Lean_Syntax_node5(v___x_4064_, v___x_4065_, v___x_4067_, v___x_3725_, v___x_4069_, v___x_4063_, v___x_4071_);
v___x_4073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4073_, 0, v___x_4072_);
leanh::lean_ctor_set(v___x_4073_, 1, v_a_3713_);
return v___x_4073_;
} else {
let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4075_: u8 = 0;
v___x_4074_ = l_Lean_Syntax_getArg(v___x_4021_, v___x_3718_);
leanh::lean_dec(v___x_4021_);
leanh::lean_inc(v___x_4074_);
v___x_4075_ = l_Lean_Syntax_matchesNull(v___x_4074_, v___x_3836_);
if v___x_4075_ == 0 {
let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4074_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4076_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4077_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4075_);
v___x_4078_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4079_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4077_, 3);
v___x_4080_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4080_, 0, v___x_4077_);
leanh::lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4082_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4082_, 0, v___x_4077_);
leanh::lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4084_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4084_, 0, v___x_4077_);
leanh::lean_ctor_set(v___x_4084_, 1, v___x_4083_);
v___x_4085_ = l_Lean_Syntax_node5(v___x_4077_, v___x_4078_, v___x_4080_, v___x_3725_, v___x_4082_, v___x_4076_, v___x_4084_);
v___x_4086_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4086_, 0, v___x_4085_);
leanh::lean_ctor_set(v___x_4086_, 1, v_a_3713_);
return v___x_4086_;
} else {
let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4088_: u8 = 0;
v___x_4087_ = l_Lean_Syntax_getArg(v___x_4074_, v___x_3724_);
v___x_4088_ = l_Lean_Syntax_matchesNull(v___x_4087_, v___x_3724_);
if v___x_4088_ == 0 {
let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4074_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4089_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4090_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4088_);
v___x_4091_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4092_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4090_, 3);
v___x_4093_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4093_, 0, v___x_4090_);
leanh::lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4095_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4095_, 0, v___x_4090_);
leanh::lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4097_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4097_, 0, v___x_4090_);
leanh::lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = l_Lean_Syntax_node5(v___x_4090_, v___x_4091_, v___x_4093_, v___x_3725_, v___x_4095_, v___x_4089_, v___x_4097_);
v___x_4099_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4099_, 0, v___x_4098_);
leanh::lean_ctor_set(v___x_4099_, 1, v_a_3713_);
return v___x_4099_;
} else {
let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4101_: u8 = 0;
v___x_4100_ = l_Lean_Syntax_getArg(v___x_4074_, v___x_3718_);
v___x_4101_ = l_Lean_Syntax_matchesNull(v___x_4100_, v___x_3724_);
if v___x_4101_ == 0 {
let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4074_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4102_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4103_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4101_);
v___x_4104_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4105_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4103_, 3);
v___x_4106_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4106_, 0, v___x_4103_);
leanh::lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4108_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4108_, 0, v___x_4103_);
leanh::lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4110_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4110_, 0, v___x_4103_);
leanh::lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_Syntax_node5(v___x_4103_, v___x_4104_, v___x_4106_, v___x_3725_, v___x_4108_, v___x_4102_, v___x_4110_);
v___x_4112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4112_, 0, v___x_4111_);
leanh::lean_ctor_set(v___x_4112_, 1, v_a_3713_);
return v___x_4112_;
} else {
let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4114_: u8 = 0;
v___x_4113_ = l_Lean_Syntax_getArg(v___x_4074_, v___x_3720_);
leanh::lean_dec(v___x_4074_);
leanh::lean_inc(v___x_4113_);
v___x_4114_ = l_Lean_Syntax_isOfKind(v___x_4113_, v___x_3876_);
if v___x_4114_ == 0 {
let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4113_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4115_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4116_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4114_);
v___x_4117_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4118_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4116_, 3);
v___x_4119_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4119_, 0, v___x_4116_);
leanh::lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4121_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4121_, 0, v___x_4116_);
leanh::lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4123_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4123_, 0, v___x_4116_);
leanh::lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l_Lean_Syntax_node5(v___x_4116_, v___x_4117_, v___x_4119_, v___x_3725_, v___x_4121_, v___x_4115_, v___x_4123_);
v___x_4125_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4125_, 0, v___x_4124_);
leanh::lean_ctor_set(v___x_4125_, 1, v_a_3713_);
return v___x_4125_;
} else {
let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4127_: u8 = 0;
v___x_4126_ = l_Lean_Syntax_getArg(v___x_4113_, v___x_3718_);
v___x_4127_ = l_Lean_Syntax_matchesNull(v___x_4126_, v___x_3724_);
if v___x_4127_ == 0 {
let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4113_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4128_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4129_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4127_);
v___x_4130_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4131_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4129_, 3);
v___x_4132_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4132_, 0, v___x_4129_);
leanh::lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4134_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4134_, 0, v___x_4129_);
leanh::lean_ctor_set(v___x_4134_, 1, v___x_4133_);
v___x_4135_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4136_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4136_, 0, v___x_4129_);
leanh::lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = l_Lean_Syntax_node5(v___x_4129_, v___x_4130_, v___x_4132_, v___x_3725_, v___x_4134_, v___x_4128_, v___x_4136_);
v___x_4138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4138_, 0, v___x_4137_);
leanh::lean_ctor_set(v___x_4138_, 1, v_a_3713_);
return v___x_4138_;
} else {
let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4141_: u8 = 0;
v___x_4139_ = l_Lean_Syntax_getArg(v___x_3725_, v___x_3836_);
v___x_4140_ = l_Std_Sat_AIG_unexpandDenote___closed__18;
leanh::lean_inc(v___x_4139_);
v___x_4141_ = l_Lean_Syntax_isOfKind(v___x_4139_, v___x_4140_);
if v___x_4141_ == 0 {
let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4139_);
leanh::lean_dec(v___x_4113_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4142_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4143_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4141_);
v___x_4144_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4145_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4143_, 3);
v___x_4146_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4146_, 0, v___x_4143_);
leanh::lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4148_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4148_, 0, v___x_4143_);
leanh::lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4150_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4150_, 0, v___x_4143_);
leanh::lean_ctor_set(v___x_4150_, 1, v___x_4149_);
v___x_4151_ = l_Lean_Syntax_node5(v___x_4143_, v___x_4144_, v___x_4146_, v___x_3725_, v___x_4148_, v___x_4142_, v___x_4150_);
v___x_4152_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4152_, 0, v___x_4151_);
leanh::lean_ctor_set(v___x_4152_, 1, v_a_3713_);
return v___x_4152_;
} else {
let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4154_: u8 = 0;
v___x_4153_ = l_Lean_Syntax_getArg(v___x_4139_, v___x_3724_);
leanh::lean_dec(v___x_4139_);
v___x_4154_ = l_Lean_Syntax_matchesNull(v___x_4153_, v___x_3724_);
if v___x_4154_ == 0 {
let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4113_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4155_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4156_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4154_);
v___x_4157_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4158_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4156_, 3);
v___x_4159_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4159_, 0, v___x_4156_);
leanh::lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4161_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4161_, 0, v___x_4156_);
leanh::lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4163_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4163_, 0, v___x_4156_);
leanh::lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = l_Lean_Syntax_node5(v___x_4156_, v___x_4157_, v___x_4159_, v___x_3725_, v___x_4161_, v___x_4155_, v___x_4163_);
v___x_4165_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4165_, 0, v___x_4164_);
leanh::lean_ctor_set(v___x_4165_, 1, v_a_3713_);
return v___x_4165_;
} else {
let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4167_: u8 = 0;
v___x_4166_ = l_Lean_Syntax_getArg(v___x_3725_, v___x_4020_);
v___x_4167_ = l_Lean_Syntax_matchesNull(v___x_4166_, v___x_3724_);
if v___x_4167_ == 0 {
let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_4113_);
leanh::lean_dec(v___x_3994_);
leanh::lean_dec(v___x_3875_);
v___x_4168_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4169_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4167_);
v___x_4170_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__4;
v___x_4171_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4169_, 3);
v___x_4172_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4172_, 0, v___x_4169_);
leanh::lean_ctor_set(v___x_4172_, 1, v___x_4171_);
v___x_4173_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4174_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4174_, 0, v___x_4169_);
leanh::lean_ctor_set(v___x_4174_, 1, v___x_4173_);
v___x_4175_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4176_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4176_, 0, v___x_4169_);
leanh::lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = l_Lean_Syntax_node5(v___x_4169_, v___x_4170_, v___x_4172_, v___x_3725_, v___x_4174_, v___x_4168_, v___x_4176_);
v___x_4178_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4178_, 0, v___x_4177_);
leanh::lean_ctor_set(v___x_4178_, 1, v_a_3713_);
return v___x_4178_;
} else {
let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4183_: u8 = 0; let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut(); let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
leanh::lean_dec(v___x_3725_);
v___x_4179_ = l_Lean_Syntax_getArg(v___x_3875_, v___x_3720_);
leanh::lean_dec(v___x_3875_);
v___x_4180_ = l_Lean_Syntax_getArg(v___x_3994_, v___x_3720_);
leanh::lean_dec(v___x_3994_);
v___x_4181_ = l_Lean_Syntax_getArg(v___x_4113_, v___x_3720_);
leanh::lean_dec(v___x_4113_);
v___x_4182_ = l_Lean_Syntax_getArg(v___x_3719_, v___x_3718_);
leanh::lean_dec(v___x_3719_);
v___x_4183_ = 0;
v___x_4184_ = l_Lean_SourceInfo_fromRef(v_a_3712_, v___x_4183_);
v___x_4185_ = l_Std_Sat_AIG_term_u27e6___x2c___x2c___u27e7___closed__1;
v___x_4186_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__7;
leanh::lean_inc_n(v___x_4184_, 7);
v___x_4187_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4187_, 0, v___x_4184_);
leanh::lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = l_Std_Sat_AIG_unexpandDenote___closed__2;
v___x_4189_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4189_, 0, v___x_4184_);
leanh::lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = l_Std_Sat_AIG_unexpandDenote___closed__20;
v___x_4191_ = l_Std_Sat_AIG_unexpandDenote___closed__21;
v___x_4192_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4192_, 0, v___x_4184_);
leanh::lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = l_Std_Sat_AIG___aux__Std__Sat__AIG__Basic______macroRules__Std__Sat__AIG__term_u27e6___x2c___u27e7__1___closed__14;
leanh::lean_inc_ref_n(v___x_4189_, 2);
v___x_4194_ = l_Lean_Syntax_node3(v___x_4184_, v___x_4193_, v___x_4180_, v___x_4189_, v___x_4181_);
v___x_4195_ = l_Std_Sat_AIG_unexpandDenote___closed__22;
v___x_4196_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4196_, 0, v___x_4184_);
leanh::lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Lean_Syntax_node3(v___x_4184_, v___x_4190_, v___x_4192_, v___x_4194_, v___x_4196_);
v___x_4198_ = l_Std_Sat_AIG_term_u27e6___x2c___u27e7___closed__17;
v___x_4199_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4199_, 0, v___x_4184_);
leanh::lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = l_Lean_Syntax_node7(v___x_4184_, v___x_4185_, v___x_4187_, v___x_4179_, v___x_4189_, v___x_4197_, v___x_4189_, v___x_4182_, v___x_4199_);
v___x_4201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
leanh::lean_ctor_set(v___x_4201_, 0, v___x_4200_);
leanh::lean_ctor_set(v___x_4201_, 1, v_a_3713_);
return v___x_4201_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_unexpandDenote___boxed(
    mut v_x_4202_: *mut leanh::LeanObject,
    mut v_a_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4205_ = l_Std_Sat_AIG_unexpandDenote(v_x_4202_, v_a_4203_, v_a_4204_);
    leanh::lean_dec(v_a_4203_);
    return v_res_4205_;
}
pub unsafe fn l_Std_Sat_AIG_mkGate___redArg(
    mut v_aig_4206_: *mut leanh::LeanObject,
    mut v_input_4207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v_decls_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v_gate_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_4219_: u8 = 0;
    let mut v_gate_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_4221_: u8 = 0;
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v_g_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: u8 = 0;
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_4208_ = leanh::lean_ctor_get(v_input_4207_, 0);
                v_rhs_4209_ = leanh::lean_ctor_get(v_input_4207_, 1);
                v_isSharedCheck_4247_ = (!leanh::lean_is_exclusive(v_input_4207_)) as u8;
                if v_isSharedCheck_4247_ == 0 {
                    v___x_4211_ = v_input_4207_;
                    v_isShared_4212_ = v_isSharedCheck_4247_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_4209_);
                    leanh::lean_inc(v_lhs_4208_);
                    leanh::lean_dec(v_input_4207_);
                    v___x_4211_ = leanh::lean_box(0);
                    v_isShared_4212_ = v_isSharedCheck_4247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_decls_4213_ = leanh::lean_ctor_get(v_aig_4206_, 0);
                v_cache_4214_ = leanh::lean_ctor_get(v_aig_4206_, 1);
                v_isSharedCheck_4246_ = (!leanh::lean_is_exclusive(v_aig_4206_)) as u8;
                if v_isSharedCheck_4246_ == 0 {
                    v___x_4216_ = v_aig_4206_;
                    v_isShared_4217_ = v_isSharedCheck_4246_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_4214_);
                    leanh::lean_inc(v_decls_4213_);
                    leanh::lean_dec(v_aig_4206_);
                    v___x_4216_ = leanh::lean_box(0);
                    v_isShared_4217_ = v_isSharedCheck_4246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_4218_ = leanh::lean_ctor_get(v_lhs_4208_, 0);
                leanh::lean_inc(v_gate_4218_);
                v_invert_4219_ = leanh::lean_ctor_get_uint8(
                    v_lhs_4208_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_lhs_4208_);
                v_gate_4220_ = leanh::lean_ctor_get(v_rhs_4209_, 0);
                v_invert_4221_ = leanh::lean_ctor_get_uint8(
                    v_rhs_4209_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4245_ = (!leanh::lean_is_exclusive(v_rhs_4209_)) as u8;
                if v_isSharedCheck_4245_ == 0 {
                    v___x_4223_ = v_rhs_4209_;
                    v_isShared_4224_ = v_isSharedCheck_4245_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_4220_);
                    leanh::lean_dec(v_rhs_4209_);
                    v___x_4223_ = leanh::lean_box(0);
                    v_isShared_4224_ = v_isSharedCheck_4245_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_g_4225_ = lean_array_get_size(v_decls_4213_);
                v___x_4226_ = leanh::lean_unsigned_to_nat(2);
                v___x_4227_ = lean_nat_mul(v_gate_4218_, v___x_4226_);
                leanh::lean_dec(v_gate_4218_);
                v___x_4228_ = l_Bool_toNat(v_invert_4219_);
                v___x_4229_ = lean_nat_lor(v___x_4227_, v___x_4228_);
                leanh::lean_dec(v___x_4228_);
                leanh::lean_dec(v___x_4227_);
                v___x_4230_ = lean_nat_mul(v_gate_4220_, v___x_4226_);
                leanh::lean_dec(v_gate_4220_);
                v___x_4231_ = l_Bool_toNat(v_invert_4221_);
                v___x_4232_ = lean_nat_lor(v___x_4230_, v___x_4231_);
                leanh::lean_dec(v___x_4231_);
                leanh::lean_dec(v___x_4230_);
                if v_isShared_4212_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4211_, 2);
                    leanh::lean_ctor_set(v___x_4211_, 1, v___x_4232_);
                    leanh::lean_ctor_set(v___x_4211_, 0, v___x_4229_);
                    v___x_4234_ = v___x_4211_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4229_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 1, v___x_4232_);
                    v___x_4234_ = v_reuseFailAlloc_4244_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_decls_4235_ = lean_array_push(v_decls_4213_, v___x_4234_);
                if v_isShared_4217_ == 0 {
                    leanh::lean_ctor_set(v___x_4216_, 0, v_decls_4235_);
                    v___x_4237_ = v___x_4216_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_decls_4235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4243_, 1, v_cache_4214_);
                    v___x_4237_ = v_reuseFailAlloc_4243_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4238_ = 0;
                if v_isShared_4224_ == 0 {
                    leanh::lean_ctor_set(v___x_4223_, 0, v_g_4225_);
                    v___x_4240_ = v___x_4223_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_g_4225_);
                    v___x_4240_ = v_reuseFailAlloc_4242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4240_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4238_,
                );
                v___x_4241_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4241_, 0, v___x_4237_);
                leanh::lean_ctor_set(v___x_4241_, 1, v___x_4240_);
                return v___x_4241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkGate(
    mut v_00_u03b1_4248_: *mut leanh::LeanObject,
    mut v_inst_4249_: *mut leanh::LeanObject,
    mut v_inst_4250_: *mut leanh::LeanObject,
    mut v_aig_4251_: *mut leanh::LeanObject,
    mut v_input_4252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4253_ = l_Std_Sat_AIG_mkGate___redArg(v_aig_4251_, v_input_4252_);
    return v___x_4253_;
}
pub unsafe fn l_Std_Sat_AIG_mkGate___boxed(
    mut v_00_u03b1_4254_: *mut leanh::LeanObject,
    mut v_inst_4255_: *mut leanh::LeanObject,
    mut v_inst_4256_: *mut leanh::LeanObject,
    mut v_aig_4257_: *mut leanh::LeanObject,
    mut v_input_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Std_Sat_AIG_mkGate(
        v_00_u03b1_4254_,
        v_inst_4255_,
        v_inst_4256_,
        v_aig_4257_,
        v_input_4258_,
    );
    leanh::lean_dec_ref(v_inst_4256_);
    leanh::lean_dec_ref(v_inst_4255_);
    return v_res_4259_;
}
pub unsafe fn l_Std_Sat_AIG_mkAtom___redArg(
    mut v_aig_4260_: *mut leanh::LeanObject,
    mut v_n_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_decls_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v_g_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_4262_ = leanh::lean_ctor_get(v_aig_4260_, 0);
                v_cache_4263_ = leanh::lean_ctor_get(v_aig_4260_, 1);
                v_isSharedCheck_4276_ = (!leanh::lean_is_exclusive(v_aig_4260_)) as u8;
                if v_isSharedCheck_4276_ == 0 {
                    v___x_4265_ = v_aig_4260_;
                    v_isShared_4266_ = v_isSharedCheck_4276_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_4263_);
                    leanh::lean_inc(v_decls_4262_);
                    leanh::lean_dec(v_aig_4260_);
                    v___x_4265_ = leanh::lean_box(0);
                    v_isShared_4266_ = v_isSharedCheck_4276_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_g_4267_ = lean_array_get_size(v_decls_4262_);
                v___x_4268_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4268_, 0, v_n_4261_);
                v_decls_4269_ = lean_array_push(v_decls_4262_, v___x_4268_);
                if v_isShared_4266_ == 0 {
                    leanh::lean_ctor_set(v___x_4265_, 0, v_decls_4269_);
                    v___x_4271_ = v___x_4265_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4275_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_decls_4269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4275_, 1, v_cache_4263_);
                    v___x_4271_ = v_reuseFailAlloc_4275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4272_ = 0;
                v___x_4273_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4273_, 0, v_g_4267_);
                leanh::lean_ctor_set_uint8(
                    v___x_4273_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4272_,
                );
                v___x_4274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4274_, 0, v___x_4271_);
                leanh::lean_ctor_set(v___x_4274_, 1, v___x_4273_);
                return v___x_4274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkAtom(
    mut v_00_u03b1_4277_: *mut leanh::LeanObject,
    mut v_inst_4278_: *mut leanh::LeanObject,
    mut v_inst_4279_: *mut leanh::LeanObject,
    mut v_aig_4280_: *mut leanh::LeanObject,
    mut v_n_4281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = l_Std_Sat_AIG_mkAtom___redArg(v_aig_4280_, v_n_4281_);
    return v___x_4282_;
}
pub unsafe fn l_Std_Sat_AIG_mkAtom___boxed(
    mut v_00_u03b1_4283_: *mut leanh::LeanObject,
    mut v_inst_4284_: *mut leanh::LeanObject,
    mut v_inst_4285_: *mut leanh::LeanObject,
    mut v_aig_4286_: *mut leanh::LeanObject,
    mut v_n_4287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4288_ = l_Std_Sat_AIG_mkAtom(
        v_00_u03b1_4283_,
        v_inst_4284_,
        v_inst_4285_,
        v_aig_4286_,
        v_n_4287_,
    );
    leanh::lean_dec_ref(v_inst_4285_);
    leanh::lean_dec_ref(v_inst_4284_);
    return v_res_4288_;
}
pub unsafe fn l_Std_Sat_AIG_mkConst___redArg(
    mut v_aig_4289_: *mut leanh::LeanObject,
    mut v_val_4290_: u8,
) -> *mut leanh::LeanObject {
    let mut v_decls_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v_g_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_4291_ = leanh::lean_ctor_get(v_aig_4289_, 0);
                v_cache_4292_ = leanh::lean_ctor_get(v_aig_4289_, 1);
                v_isSharedCheck_4304_ = (!leanh::lean_is_exclusive(v_aig_4289_)) as u8;
                if v_isSharedCheck_4304_ == 0 {
                    v___x_4294_ = v_aig_4289_;
                    v_isShared_4295_ = v_isSharedCheck_4304_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cache_4292_);
                    leanh::lean_inc(v_decls_4291_);
                    leanh::lean_dec(v_aig_4289_);
                    v___x_4294_ = leanh::lean_box(0);
                    v_isShared_4295_ = v_isSharedCheck_4304_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_g_4296_ = lean_array_get_size(v_decls_4291_);
                v___x_4297_ = leanh::lean_box(0);
                v_decls_4298_ = lean_array_push(v_decls_4291_, v___x_4297_);
                if v_isShared_4295_ == 0 {
                    leanh::lean_ctor_set(v___x_4294_, 0, v_decls_4298_);
                    v___x_4300_ = v___x_4294_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 0, v_decls_4298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4303_, 1, v_cache_4292_);
                    v___x_4300_ = v_reuseFailAlloc_4303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4301_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4301_, 0, v_g_4296_);
                leanh::lean_ctor_set_uint8(
                    v___x_4301_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_val_4290_,
                );
                v___x_4302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4302_, 0, v___x_4300_);
                leanh::lean_ctor_set(v___x_4302_, 1, v___x_4301_);
                return v___x_4302_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkConst___redArg___boxed(
    mut v_aig_4305_: *mut leanh::LeanObject,
    mut v_val_4306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_4307_: u8 = 0;
    let mut v_res_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4307_ = (leanh::lean_unbox(v_val_4306_) as u8);
    v_res_4308_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_4305_, v_val_boxed_4307_);
    return v_res_4308_;
}
pub unsafe fn l_Std_Sat_AIG_mkConst(
    mut v_00_u03b1_4309_: *mut leanh::LeanObject,
    mut v_inst_4310_: *mut leanh::LeanObject,
    mut v_inst_4311_: *mut leanh::LeanObject,
    mut v_aig_4312_: *mut leanh::LeanObject,
    mut v_val_4313_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4314_ = l_Std_Sat_AIG_mkConst___redArg(v_aig_4312_, v_val_4313_);
    return v___x_4314_;
}
pub unsafe fn l_Std_Sat_AIG_mkConst___boxed(
    mut v_00_u03b1_4315_: *mut leanh::LeanObject,
    mut v_inst_4316_: *mut leanh::LeanObject,
    mut v_inst_4317_: *mut leanh::LeanObject,
    mut v_aig_4318_: *mut leanh::LeanObject,
    mut v_val_4319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_4320_: u8 = 0;
    let mut v_res_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4320_ = (leanh::lean_unbox(v_val_4319_) as u8);
    v_res_4321_ = l_Std_Sat_AIG_mkConst(
        v_00_u03b1_4315_,
        v_inst_4316_,
        v_inst_4317_,
        v_aig_4318_,
        v_val_boxed_4320_,
    );
    leanh::lean_dec_ref(v_inst_4317_);
    leanh::lean_dec_ref(v_inst_4316_);
    return v_res_4321_;
}
pub unsafe fn l_Std_Sat_AIG_isConstant___redArg(
    mut v_aig_4322_: *mut leanh::LeanObject,
    mut v_ref_4323_: *mut leanh::LeanObject,
    mut v_b_4324_: u8,
) -> u8 {
    let mut v_gate_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_4326_: u8 = 0;
    let mut v_decls_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4330_: u8 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_gate_4325_ = leanh::lean_ctor_get(v_ref_4323_, 0);
                v_invert_4326_ = leanh::lean_ctor_get_uint8(
                    v_ref_4323_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_decls_4327_ = leanh::lean_ctor_get(v_aig_4322_, 0);
                v_decl_4328_ = lean_array_fget_borrowed(v_decls_4327_, v_gate_4325_);
                if v_invert_4326_ == 0 {
                    if v_b_4324_ == 0 {
                        v___x_4332_ = 1;
                        v___y_4330_ = v___x_4332_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4330_ = v_invert_4326_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_4330_ = v_b_4324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_decl_4328_) == 0 {
                    return v___y_4330_;
                } else {
                    v___x_4331_ = 0;
                    return v___x_4331_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_isConstant___redArg___boxed(
    mut v_aig_4333_: *mut leanh::LeanObject,
    mut v_ref_4334_: *mut leanh::LeanObject,
    mut v_b_4335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_4336_: u8 = 0;
    let mut v_res_4337_: u8 = 0;
    let mut v_r_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4336_ = (leanh::lean_unbox(v_b_4335_) as u8);
    v_res_4337_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_4333_, v_ref_4334_, v_b_boxed_4336_);
    leanh::lean_dec_ref(v_ref_4334_);
    leanh::lean_dec_ref(v_aig_4333_);
    v_r_4338_ = leanh::lean_box((v_res_4337_) as usize);
    return v_r_4338_;
}
pub unsafe fn l_Std_Sat_AIG_isConstant(
    mut v_00_u03b1_4339_: *mut leanh::LeanObject,
    mut v_inst_4340_: *mut leanh::LeanObject,
    mut v_inst_4341_: *mut leanh::LeanObject,
    mut v_aig_4342_: *mut leanh::LeanObject,
    mut v_ref_4343_: *mut leanh::LeanObject,
    mut v_b_4344_: u8,
) -> u8 {
    let mut v___x_4345_: u8 = 0;
    v___x_4345_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_4342_, v_ref_4343_, v_b_4344_);
    return v___x_4345_;
}
pub unsafe fn l_Std_Sat_AIG_isConstant___boxed(
    mut v_00_u03b1_4346_: *mut leanh::LeanObject,
    mut v_inst_4347_: *mut leanh::LeanObject,
    mut v_inst_4348_: *mut leanh::LeanObject,
    mut v_aig_4349_: *mut leanh::LeanObject,
    mut v_ref_4350_: *mut leanh::LeanObject,
    mut v_b_4351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_4352_: u8 = 0;
    let mut v_res_4353_: u8 = 0;
    let mut v_r_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_4352_ = (leanh::lean_unbox(v_b_4351_) as u8);
    v_res_4353_ = l_Std_Sat_AIG_isConstant(
        v_00_u03b1_4346_,
        v_inst_4347_,
        v_inst_4348_,
        v_aig_4349_,
        v_ref_4350_,
        v_b_boxed_4352_,
    );
    leanh::lean_dec_ref(v_ref_4350_);
    leanh::lean_dec_ref(v_aig_4349_);
    leanh::lean_dec_ref(v_inst_4348_);
    leanh::lean_dec_ref(v_inst_4347_);
    v_r_4354_ = leanh::lean_box((v_res_4353_) as usize);
    return v_r_4354_;
}
pub unsafe fn l_Std_Sat_AIG_getConstant___redArg(
    mut v_aig_4355_: *mut leanh::LeanObject,
    mut v_ref_4356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_4358_: u8 = 0;
    let mut v_decls_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_gate_4357_ = leanh::lean_ctor_get(v_ref_4356_, 0);
    v_invert_4358_ = leanh::lean_ctor_get_uint8(
        v_ref_4356_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
    );
    v_decls_4359_ = leanh::lean_ctor_get(v_aig_4355_, 0);
    v_decl_4360_ = lean_array_fget_borrowed(v_decls_4359_, v_gate_4357_);
    if leanh::lean_obj_tag(v_decl_4360_) == 0 {
        let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4361_ = leanh::lean_box((v_invert_4358_) as usize);
        v___x_4362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4362_, 0, v___x_4361_);
        return v___x_4362_;
    } else {
        let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4363_ = leanh::lean_box(0);
        return v___x_4363_;
    }
}
pub unsafe fn l_Std_Sat_AIG_getConstant___redArg___boxed(
    mut v_aig_4364_: *mut leanh::LeanObject,
    mut v_ref_4365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_4364_, v_ref_4365_);
    leanh::lean_dec_ref(v_ref_4365_);
    leanh::lean_dec_ref(v_aig_4364_);
    return v_res_4366_;
}
pub unsafe fn l_Std_Sat_AIG_getConstant(
    mut v_00_u03b1_4367_: *mut leanh::LeanObject,
    mut v_inst_4368_: *mut leanh::LeanObject,
    mut v_inst_4369_: *mut leanh::LeanObject,
    mut v_aig_4370_: *mut leanh::LeanObject,
    mut v_ref_4371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4372_ = l_Std_Sat_AIG_getConstant___redArg(v_aig_4370_, v_ref_4371_);
    return v___x_4372_;
}
pub unsafe fn l_Std_Sat_AIG_getConstant___boxed(
    mut v_00_u03b1_4373_: *mut leanh::LeanObject,
    mut v_inst_4374_: *mut leanh::LeanObject,
    mut v_inst_4375_: *mut leanh::LeanObject,
    mut v_aig_4376_: *mut leanh::LeanObject,
    mut v_ref_4377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4378_ = l_Std_Sat_AIG_getConstant(
        v_00_u03b1_4373_,
        v_inst_4374_,
        v_inst_4375_,
        v_aig_4376_,
        v_ref_4377_,
    );
    leanh::lean_dec_ref(v_ref_4377_);
    leanh::lean_dec_ref(v_aig_4376_);
    leanh::lean_dec_ref(v_inst_4375_);
    leanh::lean_dec_ref(v_inst_4374_);
    return v_res_4378_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Sat_AIG_instInhabitedFanin_default = _init_l_Std_Sat_AIG_instInhabitedFanin_default();
    leanh::lean_mark_persistent(l_Std_Sat_AIG_instInhabitedFanin_default);
    l_Std_Sat_AIG_instInhabitedFanin = _init_l_Std_Sat_AIG_instInhabitedFanin();
    leanh::lean_mark_persistent(l_Std_Sat_AIG_instInhabitedFanin);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_Basic(builtin);
}