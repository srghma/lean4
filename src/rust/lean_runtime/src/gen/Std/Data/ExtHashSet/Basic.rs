// Lean compiler output
// Module: Std.Data.ExtHashSet.Basic
// Imports: Std.Data.ExtHashMap.Basic
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Core::l_instDecidableEqPUnit___boxed;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0,
};
use crate::r#gen::Init::Data::List::Control::l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed;
use crate::r#gen::Init::Data::Nat::Power2::Basic::l_Nat_nextPowerOfTwo;
use crate::r#gen::Init::Prelude::l_instBEqOfDecidableEq___redArg___lam__0___boxed;
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Basic::{
    l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go,
    l_Std_DHashMap_Internal_AssocList_contains___redArg,
};
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_erase___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_expand___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_filter___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_inter___redArg,
};
use crate::r#gen::Std::Data::DHashMap::RawDef::l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2;
use crate::r#gen::Std::Data::ExtHashMap::Basic::{
    initialize_Std_Data_ExtHashMap_Basic, runtime_initialize_Std_Data_ExtHashMap_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_div, lean_nat_mul,
};
static mut l_Std_ExtHashSet_instEmptyCollection___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtHashSet_instEmptyCollection___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_ExtHashSet_instEmptyCollection___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_ExtHashSet_instEmptyCollection___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_ExtHashSet_ofList___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtHashSet_ofList___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtHashSet_ofList___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtHashSet_ofList___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtHashSet_ofList___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtHashSet_ofList___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtHashSet_ofList___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
static mut l_Std_ExtHashSet_ofList___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_ofList___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
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
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_ofList___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_ofList___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__10_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_ofList___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofList___redArg___closed__11_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_ofList___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_union___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_union___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_union___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_ExtHashSet_ofArray___redArg___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashSet_ofList___redArg___closed__9_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_ofArray___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofArray___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_ExtHashSet_ofArray___redArg___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instForInOfForIn_x27___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_ExtHashSet_ofArray___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_ExtHashSet_ofArray___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_ExtHashSet_ofArray___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_ExtHashSet_emptyWithCapacity___redArg(
    mut v_capacity_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_739_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_740_ = lean_nat_mul(v_capacity_737_, v___x_739_);
    v___x_741_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_742_ = lean_nat_div(v___x_740_, v___x_741_);
    crate::leanh::lean_dec(v___x_740_);
    v___x_743_ = l_Nat_nextPowerOfTwo(v___x_742_);
    crate::leanh::lean_dec(v___x_742_);
    v___x_744_ = crate::leanh::lean_box(0);
    v___x_745_ = lean_mk_array(v___x_743_, v___x_744_);
    v___x_746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_746_, 0, v___x_738_);
    crate::leanh::lean_ctor_set(v___x_746_, 1, v___x_745_);
    return v___x_746_;
}
pub unsafe fn l_Std_ExtHashSet_emptyWithCapacity___redArg___boxed(
    mut v_capacity_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Std_ExtHashSet_emptyWithCapacity___redArg(v_capacity_747_);
    crate::leanh::lean_dec(v_capacity_747_);
    return v_res_748_;
}
pub unsafe fn l_Std_ExtHashSet_emptyWithCapacity(
    mut v_00_u03b1_749_: *mut crate::leanh::LeanObject,
    mut v_inst_750_: *mut crate::leanh::LeanObject,
    mut v_inst_751_: *mut crate::leanh::LeanObject,
    mut v_capacity_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_753_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_754_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_755_ = lean_nat_mul(v_capacity_752_, v___x_754_);
    v___x_756_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_757_ = lean_nat_div(v___x_755_, v___x_756_);
    crate::leanh::lean_dec(v___x_755_);
    v___x_758_ = l_Nat_nextPowerOfTwo(v___x_757_);
    crate::leanh::lean_dec(v___x_757_);
    v___x_759_ = crate::leanh::lean_box(0);
    v___x_760_ = lean_mk_array(v___x_758_, v___x_759_);
    v___x_761_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_761_, 0, v___x_753_);
    crate::leanh::lean_ctor_set(v___x_761_, 1, v___x_760_);
    return v___x_761_;
}
pub unsafe fn l_Std_ExtHashSet_emptyWithCapacity___boxed(
    mut v_00_u03b1_762_: *mut crate::leanh::LeanObject,
    mut v_inst_763_: *mut crate::leanh::LeanObject,
    mut v_inst_764_: *mut crate::leanh::LeanObject,
    mut v_capacity_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Std_ExtHashSet_emptyWithCapacity(
        v_00_u03b1_762_,
        v_inst_763_,
        v_inst_764_,
        v_capacity_765_,
    );
    crate::leanh::lean_dec(v_capacity_765_);
    crate::leanh::lean_dec_ref(v_inst_764_);
    crate::leanh::lean_dec_ref(v_inst_763_);
    return v_res_766_;
}
pub unsafe fn _init_l_Std_ExtHashSet_instEmptyCollection___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_767_ = crate::leanh::lean_box(0);
    v___x_768_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_769_ = lean_mk_array(v___x_768_, v___x_767_);
    return v___x_769_;
}
pub unsafe fn _init_l_Std_ExtHashSet_instEmptyCollection___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__0_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__0,
    );
    v___x_771_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_772_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_772_, 0, v___x_771_);
    crate::leanh::lean_ctor_set(v___x_772_, 1, v___x_770_);
    return v___x_772_;
}
pub unsafe fn l_Std_ExtHashSet_instEmptyCollection(
    mut v_00_u03b1_773_: *mut crate::leanh::LeanObject,
    mut v_inst_774_: *mut crate::leanh::LeanObject,
    mut v_inst_775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__1,
    );
    return v___x_776_;
}
pub unsafe fn l_Std_ExtHashSet_instEmptyCollection___boxed(
    mut v_00_u03b1_777_: *mut crate::leanh::LeanObject,
    mut v_inst_778_: *mut crate::leanh::LeanObject,
    mut v_inst_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_Std_ExtHashSet_instEmptyCollection(v_00_u03b1_777_, v_inst_778_, v_inst_779_);
    crate::leanh::lean_dec_ref(v_inst_779_);
    crate::leanh::lean_dec_ref(v_inst_778_);
    return v_res_780_;
}
pub unsafe fn l_Std_ExtHashSet_instInhabited(
    mut v_00_u03b1_781_: *mut crate::leanh::LeanObject,
    mut v_inst_782_: *mut crate::leanh::LeanObject,
    mut v_inst_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_784_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__1,
    );
    return v___x_784_;
}
pub unsafe fn l_Std_ExtHashSet_instInhabited___boxed(
    mut v_00_u03b1_785_: *mut crate::leanh::LeanObject,
    mut v_inst_786_: *mut crate::leanh::LeanObject,
    mut v_inst_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_788_ = l_Std_ExtHashSet_instInhabited(v_00_u03b1_785_, v_inst_786_, v_inst_787_);
    crate::leanh::lean_dec_ref(v_inst_787_);
    crate::leanh::lean_dec_ref(v_inst_786_);
    return v_res_788_;
}
pub unsafe fn l_Std_ExtHashSet_insert___redArg(
    mut v_x_789_: *mut crate::leanh::LeanObject,
    mut v_x_790_: *mut crate::leanh::LeanObject,
    mut v_m_791_: *mut crate::leanh::LeanObject,
    mut v_a_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = crate::leanh::lean_box(0);
    v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_789_, v_x_790_, v_m_791_, v_a_792_, v___x_793_,
    );
    return v___x_794_;
}
pub unsafe fn l_Std_ExtHashSet_insert(
    mut v_00_u03b1_795_: *mut crate::leanh::LeanObject,
    mut v_x_796_: *mut crate::leanh::LeanObject,
    mut v_x_797_: *mut crate::leanh::LeanObject,
    mut v_inst_798_: *mut crate::leanh::LeanObject,
    mut v_inst_799_: *mut crate::leanh::LeanObject,
    mut v_m_800_: *mut crate::leanh::LeanObject,
    mut v_a_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = crate::leanh::lean_box(0);
    v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_796_, v_x_797_, v_m_800_, v_a_801_, v___x_802_,
    );
    return v___x_803_;
}
pub unsafe fn l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_804_: *mut crate::leanh::LeanObject,
    mut v_x_805_: *mut crate::leanh::LeanObject,
    mut v_a_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__1,
    );
    v___x_808_ = crate::leanh::lean_box(0);
    v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_804_, v_x_805_, v___x_807_, v_a_806_, v___x_808_,
    );
    return v___x_809_;
}
pub unsafe fn l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_810_: *mut crate::leanh::LeanObject,
    mut v_x_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_812_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_812_, 0, v_x_810_);
    crate::leanh::lean_closure_set(v___f_812_, 1, v_x_811_);
    return v___f_812_;
}
pub unsafe fn l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_813_: *mut crate::leanh::LeanObject,
    mut v_x_814_: *mut crate::leanh::LeanObject,
    mut v_x_815_: *mut crate::leanh::LeanObject,
    mut v_inst_816_: *mut crate::leanh::LeanObject,
    mut v_inst_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_818_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_instSingletonOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_818_, 0, v_x_814_);
    crate::leanh::lean_closure_set(v___f_818_, 1, v_x_815_);
    return v___f_818_;
}
pub unsafe fn l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_819_: *mut crate::leanh::LeanObject,
    mut v_x_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_s_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_823_ = crate::leanh::lean_box(0);
    v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_819_, v_x_820_, v_s_822_, v_a_821_, v___x_823_,
    );
    return v___x_824_;
}
pub unsafe fn l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_825_: *mut crate::leanh::LeanObject,
    mut v_x_826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_827_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_827_, 0, v_x_825_);
    crate::leanh::lean_closure_set(v___f_827_, 1, v_x_826_);
    return v___f_827_;
}
pub unsafe fn l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_828_: *mut crate::leanh::LeanObject,
    mut v_x_829_: *mut crate::leanh::LeanObject,
    mut v_x_830_: *mut crate::leanh::LeanObject,
    mut v_inst_831_: *mut crate::leanh::LeanObject,
    mut v_inst_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_833_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_instInsertOfEquivBEqOfLawfulHashable___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_833_, 0, v_x_829_);
    crate::leanh::lean_closure_set(v___f_833_, 1, v_x_830_);
    return v___f_833_;
}
pub unsafe fn l_Std_ExtHashSet_containsThenInsert___redArg(
    mut v_x_834_: *mut crate::leanh::LeanObject,
    mut v_x_835_: *mut crate::leanh::LeanObject,
    mut v_m_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: u64 = 0;
    let mut v___x_843_: u64 = 0;
    let mut v___x_844_: u64 = 0;
    let mut v___x_845_: u64 = 0;
    let mut v_fold_846_: u64 = 0;
    let mut v___x_847_: u64 = 0;
    let mut v___x_848_: u64 = 0;
    let mut v___x_849_: u64 = 0;
    let mut v___x_850_: usize = 0;
    let mut v___x_851_: usize = 0;
    let mut v___x_852_: usize = 0;
    let mut v___x_853_: usize = 0;
    let mut v___x_854_: usize = 0;
    let mut v_bkt_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: u8 = 0;
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: u8 = 0;
    let mut v_val_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v_unused_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_838_ = crate::leanh::lean_ctor_get(v_m_836_, 0);
                v_buckets_839_ = crate::leanh::lean_ctor_get(v_m_836_, 1);
                v___x_840_ = lean_array_get_size(v_buckets_839_);
                crate::leanh::lean_inc_ref(v_x_835_);
                crate::leanh::lean_inc_n(v_a_837_, 2);
                v___x_841_ = crate::leanh::lean_apply_1(v_x_835_, v_a_837_);
                v___x_842_ = 32u64;
                v___x_843_ = crate::leanh::lean_unbox_uint64(v___x_841_);
                v___x_844_ = lean_uint64_shift_right(v___x_843_, v___x_842_);
                v___x_845_ = crate::leanh::lean_unbox_uint64(v___x_841_);
                crate::leanh::lean_dec_ref(v___x_841_);
                v_fold_846_ = lean_uint64_xor(v___x_845_, v___x_844_);
                v___x_847_ = 16u64;
                v___x_848_ = lean_uint64_shift_right(v_fold_846_, v___x_847_);
                v___x_849_ = lean_uint64_xor(v_fold_846_, v___x_848_);
                v___x_850_ = lean_uint64_to_usize(v___x_849_);
                v___x_851_ = lean_usize_of_nat(v___x_840_);
                v___x_852_ = 1usize;
                v___x_853_ = lean_usize_sub(v___x_851_, v___x_852_);
                v___x_854_ = lean_usize_land(v___x_850_, v___x_853_);
                v_bkt_855_ = lean_array_uget_borrowed(v_buckets_839_, v___x_854_);
                crate::leanh::lean_inc(v_bkt_855_);
                v___x_856_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_834_, v_a_837_, v_bkt_855_,
                );
                if v___x_856_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_839_);
                    crate::leanh::lean_inc(v_size_838_);
                    v_isSharedCheck_882_ = (!crate::leanh::lean_is_exclusive(v_m_836_)) as u8;
                    if v_isSharedCheck_882_ == 0 {
                        v_unused_883_ = crate::leanh::lean_ctor_get(v_m_836_, 1);
                        crate::leanh::lean_dec(v_unused_883_);
                        v_unused_884_ = crate::leanh::lean_ctor_get(v_m_836_, 0);
                        crate::leanh::lean_dec(v_unused_884_);
                        v___x_858_ = v_m_836_;
                        v_isShared_859_ = v_isSharedCheck_882_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_836_);
                        v___x_858_ = crate::leanh::lean_box(0);
                        v_isShared_859_ = v_isSharedCheck_882_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_837_);
                    crate::leanh::lean_dec_ref(v_x_835_);
                    v___x_885_ = crate::leanh::lean_box((v___x_856_) as usize);
                    v___x_886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_886_, 0, v___x_885_);
                    crate::leanh::lean_ctor_set(v___x_886_, 1, v_m_836_);
                    return v___x_886_;
                }
            }
            1 => {
                v___x_860_ = crate::leanh::lean_box(0);
                v___x_861_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_862_ = lean_nat_add(v_size_838_, v___x_861_);
                crate::leanh::lean_dec(v_size_838_);
                crate::leanh::lean_inc(v_bkt_855_);
                v___x_863_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_863_, 0, v_a_837_);
                crate::leanh::lean_ctor_set(v___x_863_, 1, v___x_860_);
                crate::leanh::lean_ctor_set(v___x_863_, 2, v_bkt_855_);
                v_buckets_x27_864_ = lean_array_uset(v_buckets_839_, v___x_854_, v___x_863_);
                v___x_865_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_866_ = lean_nat_mul(v_size_x27_862_, v___x_865_);
                v___x_867_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_868_ = lean_nat_div(v___x_866_, v___x_867_);
                crate::leanh::lean_dec(v___x_866_);
                v___x_869_ = lean_array_get_size(v_buckets_x27_864_);
                v___x_870_ = lean_nat_dec_le(v___x_868_, v___x_869_);
                crate::leanh::lean_dec(v___x_868_);
                if v___x_870_ == 0 {
                    v_val_871_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_835_,
                        v_buckets_x27_864_,
                    );
                    if v_isShared_859_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_858_, 1, v_val_871_);
                        crate::leanh::lean_ctor_set(v___x_858_, 0, v_size_x27_862_);
                        v___x_873_ = v___x_858_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_876_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 0, v_size_x27_862_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 1, v_val_871_);
                        v___x_873_ = v_reuseFailAlloc_876_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_835_);
                    if v_isShared_859_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_858_, 1, v_buckets_x27_864_);
                        crate::leanh::lean_ctor_set(v___x_858_, 0, v_size_x27_862_);
                        v___x_878_ = v___x_858_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_881_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v_size_x27_862_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 1, v_buckets_x27_864_);
                        v___x_878_ = v_reuseFailAlloc_881_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_874_ = crate::leanh::lean_box((v___x_856_) as usize);
                v___x_875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_875_, 0, v___x_874_);
                crate::leanh::lean_ctor_set(v___x_875_, 1, v___x_873_);
                return v___x_875_;
            }
            3 => {
                v___x_879_ = crate::leanh::lean_box((v___x_856_) as usize);
                v___x_880_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_880_, 0, v___x_879_);
                crate::leanh::lean_ctor_set(v___x_880_, 1, v___x_878_);
                return v___x_880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashSet_containsThenInsert(
    mut v_00_u03b1_887_: *mut crate::leanh::LeanObject,
    mut v_x_888_: *mut crate::leanh::LeanObject,
    mut v_x_889_: *mut crate::leanh::LeanObject,
    mut v_inst_890_: *mut crate::leanh::LeanObject,
    mut v_inst_891_: *mut crate::leanh::LeanObject,
    mut v_m_892_: *mut crate::leanh::LeanObject,
    mut v_a_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u64 = 0;
    let mut v___x_899_: u64 = 0;
    let mut v___x_900_: u64 = 0;
    let mut v___x_901_: u64 = 0;
    let mut v_fold_902_: u64 = 0;
    let mut v___x_903_: u64 = 0;
    let mut v___x_904_: u64 = 0;
    let mut v___x_905_: u64 = 0;
    let mut v___x_906_: usize = 0;
    let mut v___x_907_: usize = 0;
    let mut v___x_908_: usize = 0;
    let mut v___x_909_: usize = 0;
    let mut v___x_910_: usize = 0;
    let mut v_bkt_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: u8 = 0;
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: u8 = 0;
    let mut v_val_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_938_: u8 = 0;
    let mut v_unused_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_894_ = crate::leanh::lean_ctor_get(v_m_892_, 0);
                v_buckets_895_ = crate::leanh::lean_ctor_get(v_m_892_, 1);
                v___x_896_ = lean_array_get_size(v_buckets_895_);
                crate::leanh::lean_inc_ref(v_x_889_);
                crate::leanh::lean_inc_n(v_a_893_, 2);
                v___x_897_ = crate::leanh::lean_apply_1(v_x_889_, v_a_893_);
                v___x_898_ = 32u64;
                v___x_899_ = crate::leanh::lean_unbox_uint64(v___x_897_);
                v___x_900_ = lean_uint64_shift_right(v___x_899_, v___x_898_);
                v___x_901_ = crate::leanh::lean_unbox_uint64(v___x_897_);
                crate::leanh::lean_dec_ref(v___x_897_);
                v_fold_902_ = lean_uint64_xor(v___x_901_, v___x_900_);
                v___x_903_ = 16u64;
                v___x_904_ = lean_uint64_shift_right(v_fold_902_, v___x_903_);
                v___x_905_ = lean_uint64_xor(v_fold_902_, v___x_904_);
                v___x_906_ = lean_uint64_to_usize(v___x_905_);
                v___x_907_ = lean_usize_of_nat(v___x_896_);
                v___x_908_ = 1usize;
                v___x_909_ = lean_usize_sub(v___x_907_, v___x_908_);
                v___x_910_ = lean_usize_land(v___x_906_, v___x_909_);
                v_bkt_911_ = lean_array_uget_borrowed(v_buckets_895_, v___x_910_);
                crate::leanh::lean_inc(v_bkt_911_);
                v___x_912_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(
                    v_x_888_, v_a_893_, v_bkt_911_,
                );
                if v___x_912_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_895_);
                    crate::leanh::lean_inc(v_size_894_);
                    v_isSharedCheck_938_ = (!crate::leanh::lean_is_exclusive(v_m_892_)) as u8;
                    if v_isSharedCheck_938_ == 0 {
                        v_unused_939_ = crate::leanh::lean_ctor_get(v_m_892_, 1);
                        crate::leanh::lean_dec(v_unused_939_);
                        v_unused_940_ = crate::leanh::lean_ctor_get(v_m_892_, 0);
                        crate::leanh::lean_dec(v_unused_940_);
                        v___x_914_ = v_m_892_;
                        v_isShared_915_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_892_);
                        v___x_914_ = crate::leanh::lean_box(0);
                        v_isShared_915_ = v_isSharedCheck_938_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_893_);
                    crate::leanh::lean_dec_ref(v_x_889_);
                    v___x_941_ = crate::leanh::lean_box((v___x_912_) as usize);
                    v___x_942_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_942_, 0, v___x_941_);
                    crate::leanh::lean_ctor_set(v___x_942_, 1, v_m_892_);
                    return v___x_942_;
                }
            }
            1 => {
                v___x_916_ = crate::leanh::lean_box(0);
                v___x_917_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_918_ = lean_nat_add(v_size_894_, v___x_917_);
                crate::leanh::lean_dec(v_size_894_);
                crate::leanh::lean_inc(v_bkt_911_);
                v___x_919_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_919_, 0, v_a_893_);
                crate::leanh::lean_ctor_set(v___x_919_, 1, v___x_916_);
                crate::leanh::lean_ctor_set(v___x_919_, 2, v_bkt_911_);
                v_buckets_x27_920_ = lean_array_uset(v_buckets_895_, v___x_910_, v___x_919_);
                v___x_921_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_922_ = lean_nat_mul(v_size_x27_918_, v___x_921_);
                v___x_923_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_924_ = lean_nat_div(v___x_922_, v___x_923_);
                crate::leanh::lean_dec(v___x_922_);
                v___x_925_ = lean_array_get_size(v_buckets_x27_920_);
                v___x_926_ = lean_nat_dec_le(v___x_924_, v___x_925_);
                crate::leanh::lean_dec(v___x_924_);
                if v___x_926_ == 0 {
                    v_val_927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(
                        v_x_889_,
                        v_buckets_x27_920_,
                    );
                    if v_isShared_915_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_914_, 1, v_val_927_);
                        crate::leanh::lean_ctor_set(v___x_914_, 0, v_size_x27_918_);
                        v___x_929_ = v___x_914_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v_size_x27_918_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 1, v_val_927_);
                        v___x_929_ = v_reuseFailAlloc_932_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_889_);
                    if v_isShared_915_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_914_, 1, v_buckets_x27_920_);
                        crate::leanh::lean_ctor_set(v___x_914_, 0, v_size_x27_918_);
                        v___x_934_ = v___x_914_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_937_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_937_, 0, v_size_x27_918_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_937_, 1, v_buckets_x27_920_);
                        v___x_934_ = v_reuseFailAlloc_937_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_930_ = crate::leanh::lean_box((v___x_912_) as usize);
                v___x_931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_931_, 0, v___x_930_);
                crate::leanh::lean_ctor_set(v___x_931_, 1, v___x_929_);
                return v___x_931_;
            }
            3 => {
                v___x_935_ = crate::leanh::lean_box((v___x_912_) as usize);
                v___x_936_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_935_);
                crate::leanh::lean_ctor_set(v___x_936_, 1, v___x_934_);
                return v___x_936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_ExtHashSet_contains___redArg(
    mut v_x_943_: *mut crate::leanh::LeanObject,
    mut v_x_944_: *mut crate::leanh::LeanObject,
    mut v_m_945_: *mut crate::leanh::LeanObject,
    mut v_a_946_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_947_: u8 = 0;
    v___x_947_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_943_, v_x_944_, v_m_945_, v_a_946_);
    return v___x_947_;
}
pub unsafe fn l_Std_ExtHashSet_contains___redArg___boxed(
    mut v_x_948_: *mut crate::leanh::LeanObject,
    mut v_x_949_: *mut crate::leanh::LeanObject,
    mut v_m_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_952_: u8 = 0;
    let mut v_r_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Std_ExtHashSet_contains___redArg(v_x_948_, v_x_949_, v_m_950_, v_a_951_);
    crate::leanh::lean_dec(v_m_950_);
    v_r_953_ = crate::leanh::lean_box((v_res_952_) as usize);
    return v_r_953_;
}
pub unsafe fn l_Std_ExtHashSet_contains(
    mut v_00_u03b1_954_: *mut crate::leanh::LeanObject,
    mut v_x_955_: *mut crate::leanh::LeanObject,
    mut v_x_956_: *mut crate::leanh::LeanObject,
    mut v_inst_957_: *mut crate::leanh::LeanObject,
    mut v_inst_958_: *mut crate::leanh::LeanObject,
    mut v_m_959_: *mut crate::leanh::LeanObject,
    mut v_a_960_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_961_: u8 = 0;
    v___x_961_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_955_, v_x_956_, v_m_959_, v_a_960_);
    return v___x_961_;
}
pub unsafe fn l_Std_ExtHashSet_contains___boxed(
    mut v_00_u03b1_962_: *mut crate::leanh::LeanObject,
    mut v_x_963_: *mut crate::leanh::LeanObject,
    mut v_x_964_: *mut crate::leanh::LeanObject,
    mut v_inst_965_: *mut crate::leanh::LeanObject,
    mut v_inst_966_: *mut crate::leanh::LeanObject,
    mut v_m_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_969_: u8 = 0;
    let mut v_r_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_969_ = l_Std_ExtHashSet_contains(
        v_00_u03b1_962_,
        v_x_963_,
        v_x_964_,
        v_inst_965_,
        v_inst_966_,
        v_m_967_,
        v_a_968_,
    );
    crate::leanh::lean_dec(v_m_967_);
    v_r_970_ = crate::leanh::lean_box((v_res_969_) as usize);
    return v_r_970_;
}
pub unsafe fn l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_971_: *mut crate::leanh::LeanObject,
    mut v_inst_972_: *mut crate::leanh::LeanObject,
    mut v_inst_973_: *mut crate::leanh::LeanObject,
    mut v_inst_974_: *mut crate::leanh::LeanObject,
    mut v_inst_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ = crate::leanh::lean_box(0);
    return v___x_976_;
}
pub unsafe fn l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable___boxed(
    mut v_00_u03b1_977_: *mut crate::leanh::LeanObject,
    mut v_inst_978_: *mut crate::leanh::LeanObject,
    mut v_inst_979_: *mut crate::leanh::LeanObject,
    mut v_inst_980_: *mut crate::leanh::LeanObject,
    mut v_inst_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Std_ExtHashSet_instMembershipOfEquivBEqOfLawfulHashable(
        v_00_u03b1_977_,
        v_inst_978_,
        v_inst_979_,
        v_inst_980_,
        v_inst_981_,
    );
    crate::leanh::lean_dec_ref(v_inst_979_);
    crate::leanh::lean_dec_ref(v_inst_978_);
    return v_res_982_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableMem___redArg(
    mut v_inst_983_: *mut crate::leanh::LeanObject,
    mut v_inst_984_: *mut crate::leanh::LeanObject,
    mut v_m_985_: *mut crate::leanh::LeanObject,
    mut v_a_986_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_987_: u8 = 0;
    v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_983_,
        v_inst_984_,
        v_m_985_,
        v_a_986_,
    );
    return v___x_987_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableMem___redArg___boxed(
    mut v_inst_988_: *mut crate::leanh::LeanObject,
    mut v_inst_989_: *mut crate::leanh::LeanObject,
    mut v_m_990_: *mut crate::leanh::LeanObject,
    mut v_a_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_992_: u8 = 0;
    let mut v_r_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_992_ =
        l_Std_ExtHashSet_instDecidableMem___redArg(v_inst_988_, v_inst_989_, v_m_990_, v_a_991_);
    crate::leanh::lean_dec(v_m_990_);
    v_r_993_ = crate::leanh::lean_box((v_res_992_) as usize);
    return v_r_993_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableMem(
    mut v_00_u03b1_994_: *mut crate::leanh::LeanObject,
    mut v_inst_995_: *mut crate::leanh::LeanObject,
    mut v_inst_996_: *mut crate::leanh::LeanObject,
    mut v_inst_997_: *mut crate::leanh::LeanObject,
    mut v_inst_998_: *mut crate::leanh::LeanObject,
    mut v_m_999_: *mut crate::leanh::LeanObject,
    mut v_a_1000_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1001_: u8 = 0;
    v___x_1001_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_inst_995_,
        v_inst_996_,
        v_m_999_,
        v_a_1000_,
    );
    return v___x_1001_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableMem___boxed(
    mut v_00_u03b1_1002_: *mut crate::leanh::LeanObject,
    mut v_inst_1003_: *mut crate::leanh::LeanObject,
    mut v_inst_1004_: *mut crate::leanh::LeanObject,
    mut v_inst_1005_: *mut crate::leanh::LeanObject,
    mut v_inst_1006_: *mut crate::leanh::LeanObject,
    mut v_m_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1009_: u8 = 0;
    let mut v_r_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = l_Std_ExtHashSet_instDecidableMem(
        v_00_u03b1_1002_,
        v_inst_1003_,
        v_inst_1004_,
        v_inst_1005_,
        v_inst_1006_,
        v_m_1007_,
        v_a_1008_,
    );
    crate::leanh::lean_dec(v_m_1007_);
    v_r_1010_ = crate::leanh::lean_box((v_res_1009_) as usize);
    return v_r_1010_;
}
pub unsafe fn l_Std_ExtHashSet_erase___redArg(
    mut v_x_1011_: *mut crate::leanh::LeanObject,
    mut v_x_1012_: *mut crate::leanh::LeanObject,
    mut v_m_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_1011_, v_x_1012_, v_m_1013_, v_a_1014_,
    );
    return v___x_1015_;
}
pub unsafe fn l_Std_ExtHashSet_erase(
    mut v_00_u03b1_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
    mut v_x_1018_: *mut crate::leanh::LeanObject,
    mut v_inst_1019_: *mut crate::leanh::LeanObject,
    mut v_inst_1020_: *mut crate::leanh::LeanObject,
    mut v_m_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(
        v_x_1017_, v_x_1018_, v_m_1021_, v_a_1022_,
    );
    return v___x_1023_;
}
pub unsafe fn l_Std_ExtHashSet_size___redArg(
    mut v_m_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_1025_ = crate::leanh::lean_ctor_get(v_m_1024_, 0);
    crate::leanh::lean_inc(v_size_1025_);
    return v_size_1025_;
}
pub unsafe fn l_Std_ExtHashSet_size___redArg___boxed(
    mut v_m_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1027_ = l_Std_ExtHashSet_size___redArg(v_m_1026_);
    crate::leanh::lean_dec(v_m_1026_);
    return v_res_1027_;
}
pub unsafe fn l_Std_ExtHashSet_size(
    mut v_00_u03b1_1028_: *mut crate::leanh::LeanObject,
    mut v_x_1029_: *mut crate::leanh::LeanObject,
    mut v_x_1030_: *mut crate::leanh::LeanObject,
    mut v_inst_1031_: *mut crate::leanh::LeanObject,
    mut v_inst_1032_: *mut crate::leanh::LeanObject,
    mut v_m_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_1034_ = crate::leanh::lean_ctor_get(v_m_1033_, 0);
    crate::leanh::lean_inc(v_size_1034_);
    return v_size_1034_;
}
pub unsafe fn l_Std_ExtHashSet_size___boxed(
    mut v_00_u03b1_1035_: *mut crate::leanh::LeanObject,
    mut v_x_1036_: *mut crate::leanh::LeanObject,
    mut v_x_1037_: *mut crate::leanh::LeanObject,
    mut v_inst_1038_: *mut crate::leanh::LeanObject,
    mut v_inst_1039_: *mut crate::leanh::LeanObject,
    mut v_m_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1041_ = l_Std_ExtHashSet_size(
        v_00_u03b1_1035_,
        v_x_1036_,
        v_x_1037_,
        v_inst_1038_,
        v_inst_1039_,
        v_m_1040_,
    );
    crate::leanh::lean_dec(v_m_1040_);
    crate::leanh::lean_dec_ref(v_x_1037_);
    crate::leanh::lean_dec_ref(v_x_1036_);
    return v_res_1041_;
}
pub unsafe fn l_Std_ExtHashSet_get_x3f___redArg(
    mut v_x_1042_: *mut crate::leanh::LeanObject,
    mut v_x_1043_: *mut crate::leanh::LeanObject,
    mut v_m_1044_: *mut crate::leanh::LeanObject,
    mut v_a_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_1042_, v_x_1043_, v_m_1044_, v_a_1045_,
    );
    return v___x_1046_;
}
pub unsafe fn l_Std_ExtHashSet_get_x3f___redArg___boxed(
    mut v_x_1047_: *mut crate::leanh::LeanObject,
    mut v_x_1048_: *mut crate::leanh::LeanObject,
    mut v_m_1049_: *mut crate::leanh::LeanObject,
    mut v_a_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_Std_ExtHashSet_get_x3f___redArg(v_x_1047_, v_x_1048_, v_m_1049_, v_a_1050_);
    crate::leanh::lean_dec(v_m_1049_);
    return v_res_1051_;
}
pub unsafe fn l_Std_ExtHashSet_get_x3f(
    mut v_00_u03b1_1052_: *mut crate::leanh::LeanObject,
    mut v_x_1053_: *mut crate::leanh::LeanObject,
    mut v_x_1054_: *mut crate::leanh::LeanObject,
    mut v_inst_1055_: *mut crate::leanh::LeanObject,
    mut v_inst_1056_: *mut crate::leanh::LeanObject,
    mut v_m_1057_: *mut crate::leanh::LeanObject,
    mut v_a_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(
        v_x_1053_, v_x_1054_, v_m_1057_, v_a_1058_,
    );
    return v___x_1059_;
}
pub unsafe fn l_Std_ExtHashSet_get_x3f___boxed(
    mut v_00_u03b1_1060_: *mut crate::leanh::LeanObject,
    mut v_x_1061_: *mut crate::leanh::LeanObject,
    mut v_x_1062_: *mut crate::leanh::LeanObject,
    mut v_inst_1063_: *mut crate::leanh::LeanObject,
    mut v_inst_1064_: *mut crate::leanh::LeanObject,
    mut v_m_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_Std_ExtHashSet_get_x3f(
        v_00_u03b1_1060_,
        v_x_1061_,
        v_x_1062_,
        v_inst_1063_,
        v_inst_1064_,
        v_m_1065_,
        v_a_1066_,
    );
    crate::leanh::lean_dec(v_m_1065_);
    return v_res_1067_;
}
pub unsafe fn l_Std_ExtHashSet_get___redArg(
    mut v_x_1068_: *mut crate::leanh::LeanObject,
    mut v_x_1069_: *mut crate::leanh::LeanObject,
    mut v_m_1070_: *mut crate::leanh::LeanObject,
    mut v_a_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_1068_, v_x_1069_, v_m_1070_, v_a_1071_,
    );
    return v___x_1072_;
}
pub unsafe fn l_Std_ExtHashSet_get___redArg___boxed(
    mut v_x_1073_: *mut crate::leanh::LeanObject,
    mut v_x_1074_: *mut crate::leanh::LeanObject,
    mut v_m_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Std_ExtHashSet_get___redArg(v_x_1073_, v_x_1074_, v_m_1075_, v_a_1076_);
    crate::leanh::lean_dec(v_m_1075_);
    return v_res_1077_;
}
pub unsafe fn l_Std_ExtHashSet_get(
    mut v_00_u03b1_1078_: *mut crate::leanh::LeanObject,
    mut v_x_1079_: *mut crate::leanh::LeanObject,
    mut v_x_1080_: *mut crate::leanh::LeanObject,
    mut v_inst_1081_: *mut crate::leanh::LeanObject,
    mut v_inst_1082_: *mut crate::leanh::LeanObject,
    mut v_m_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_h_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(
        v_x_1079_, v_x_1080_, v_m_1083_, v_a_1084_,
    );
    return v___x_1086_;
}
pub unsafe fn l_Std_ExtHashSet_get___boxed(
    mut v_00_u03b1_1087_: *mut crate::leanh::LeanObject,
    mut v_x_1088_: *mut crate::leanh::LeanObject,
    mut v_x_1089_: *mut crate::leanh::LeanObject,
    mut v_inst_1090_: *mut crate::leanh::LeanObject,
    mut v_inst_1091_: *mut crate::leanh::LeanObject,
    mut v_m_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_h_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_Std_ExtHashSet_get(
        v_00_u03b1_1087_,
        v_x_1088_,
        v_x_1089_,
        v_inst_1090_,
        v_inst_1091_,
        v_m_1092_,
        v_a_1093_,
        v_h_1094_,
    );
    crate::leanh::lean_dec(v_m_1092_);
    return v_res_1095_;
}
pub unsafe fn l_Std_ExtHashSet_getD___redArg(
    mut v_x_1096_: *mut crate::leanh::LeanObject,
    mut v_x_1097_: *mut crate::leanh::LeanObject,
    mut v_m_1098_: *mut crate::leanh::LeanObject,
    mut v_a_1099_: *mut crate::leanh::LeanObject,
    mut v_fallback_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_1096_,
        v_x_1097_,
        v_m_1098_,
        v_a_1099_,
        v_fallback_1100_,
    );
    return v___x_1101_;
}
pub unsafe fn l_Std_ExtHashSet_getD___redArg___boxed(
    mut v_x_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: *mut crate::leanh::LeanObject,
    mut v_m_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_fallback_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l_Std_ExtHashSet_getD___redArg(
        v_x_1102_,
        v_x_1103_,
        v_m_1104_,
        v_a_1105_,
        v_fallback_1106_,
    );
    crate::leanh::lean_dec(v_fallback_1106_);
    crate::leanh::lean_dec(v_m_1104_);
    return v_res_1107_;
}
pub unsafe fn l_Std_ExtHashSet_getD(
    mut v_00_u03b1_1108_: *mut crate::leanh::LeanObject,
    mut v_x_1109_: *mut crate::leanh::LeanObject,
    mut v_x_1110_: *mut crate::leanh::LeanObject,
    mut v_inst_1111_: *mut crate::leanh::LeanObject,
    mut v_inst_1112_: *mut crate::leanh::LeanObject,
    mut v_m_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_fallback_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(
        v_x_1109_,
        v_x_1110_,
        v_m_1113_,
        v_a_1114_,
        v_fallback_1115_,
    );
    return v___x_1116_;
}
pub unsafe fn l_Std_ExtHashSet_getD___boxed(
    mut v_00_u03b1_1117_: *mut crate::leanh::LeanObject,
    mut v_x_1118_: *mut crate::leanh::LeanObject,
    mut v_x_1119_: *mut crate::leanh::LeanObject,
    mut v_inst_1120_: *mut crate::leanh::LeanObject,
    mut v_inst_1121_: *mut crate::leanh::LeanObject,
    mut v_m_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_fallback_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_Std_ExtHashSet_getD(
        v_00_u03b1_1117_,
        v_x_1118_,
        v_x_1119_,
        v_inst_1120_,
        v_inst_1121_,
        v_m_1122_,
        v_a_1123_,
        v_fallback_1124_,
    );
    crate::leanh::lean_dec(v_fallback_1124_);
    crate::leanh::lean_dec(v_m_1122_);
    return v_res_1125_;
}
pub unsafe fn l_Std_ExtHashSet_get_x21___redArg(
    mut v_x_1126_: *mut crate::leanh::LeanObject,
    mut v_x_1127_: *mut crate::leanh::LeanObject,
    mut v_inst_1128_: *mut crate::leanh::LeanObject,
    mut v_m_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_1126_,
        v_x_1127_,
        v_inst_1128_,
        v_m_1129_,
        v_a_1130_,
    );
    return v___x_1131_;
}
pub unsafe fn l_Std_ExtHashSet_get_x21___redArg___boxed(
    mut v_x_1132_: *mut crate::leanh::LeanObject,
    mut v_x_1133_: *mut crate::leanh::LeanObject,
    mut v_inst_1134_: *mut crate::leanh::LeanObject,
    mut v_m_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ =
        l_Std_ExtHashSet_get_x21___redArg(v_x_1132_, v_x_1133_, v_inst_1134_, v_m_1135_, v_a_1136_);
    crate::leanh::lean_dec(v_m_1135_);
    crate::leanh::lean_dec(v_inst_1134_);
    return v_res_1137_;
}
pub unsafe fn l_Std_ExtHashSet_get_x21(
    mut v_00_u03b1_1138_: *mut crate::leanh::LeanObject,
    mut v_x_1139_: *mut crate::leanh::LeanObject,
    mut v_x_1140_: *mut crate::leanh::LeanObject,
    mut v_inst_1141_: *mut crate::leanh::LeanObject,
    mut v_inst_1142_: *mut crate::leanh::LeanObject,
    mut v_inst_1143_: *mut crate::leanh::LeanObject,
    mut v_m_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(
        v_x_1139_,
        v_x_1140_,
        v_inst_1143_,
        v_m_1144_,
        v_a_1145_,
    );
    return v___x_1146_;
}
pub unsafe fn l_Std_ExtHashSet_get_x21___boxed(
    mut v_00_u03b1_1147_: *mut crate::leanh::LeanObject,
    mut v_x_1148_: *mut crate::leanh::LeanObject,
    mut v_x_1149_: *mut crate::leanh::LeanObject,
    mut v_inst_1150_: *mut crate::leanh::LeanObject,
    mut v_inst_1151_: *mut crate::leanh::LeanObject,
    mut v_inst_1152_: *mut crate::leanh::LeanObject,
    mut v_m_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Std_ExtHashSet_get_x21(
        v_00_u03b1_1147_,
        v_x_1148_,
        v_x_1149_,
        v_inst_1150_,
        v_inst_1151_,
        v_inst_1152_,
        v_m_1153_,
        v_a_1154_,
    );
    crate::leanh::lean_dec(v_m_1153_);
    crate::leanh::lean_dec(v_inst_1152_);
    return v_res_1155_;
}
pub unsafe fn l_Std_ExtHashSet_isEmpty___redArg(
    mut v_m_1156_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    v_size_1157_ = crate::leanh::lean_ctor_get(v_m_1156_, 0);
    v___x_1158_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1159_ = lean_nat_dec_eq(v_size_1157_, v___x_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_ExtHashSet_isEmpty___redArg___boxed(
    mut v_m_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1161_: u8 = 0;
    let mut v_r_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1161_ = l_Std_ExtHashSet_isEmpty___redArg(v_m_1160_);
    crate::leanh::lean_dec(v_m_1160_);
    v_r_1162_ = crate::leanh::lean_box((v_res_1161_) as usize);
    return v_r_1162_;
}
pub unsafe fn l_Std_ExtHashSet_isEmpty(
    mut v_00_u03b1_1163_: *mut crate::leanh::LeanObject,
    mut v_x_1164_: *mut crate::leanh::LeanObject,
    mut v_x_1165_: *mut crate::leanh::LeanObject,
    mut v_inst_1166_: *mut crate::leanh::LeanObject,
    mut v_inst_1167_: *mut crate::leanh::LeanObject,
    mut v_m_1168_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u8 = 0;
    v_size_1169_ = crate::leanh::lean_ctor_get(v_m_1168_, 0);
    v___x_1170_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1171_ = lean_nat_dec_eq(v_size_1169_, v___x_1170_);
    return v___x_1171_;
}
pub unsafe fn l_Std_ExtHashSet_isEmpty___boxed(
    mut v_00_u03b1_1172_: *mut crate::leanh::LeanObject,
    mut v_x_1173_: *mut crate::leanh::LeanObject,
    mut v_x_1174_: *mut crate::leanh::LeanObject,
    mut v_inst_1175_: *mut crate::leanh::LeanObject,
    mut v_inst_1176_: *mut crate::leanh::LeanObject,
    mut v_m_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1178_: u8 = 0;
    let mut v_r_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Std_ExtHashSet_isEmpty(
        v_00_u03b1_1172_,
        v_x_1173_,
        v_x_1174_,
        v_inst_1175_,
        v_inst_1176_,
        v_m_1177_,
    );
    crate::leanh::lean_dec(v_m_1177_);
    crate::leanh::lean_dec_ref(v_x_1174_);
    crate::leanh::lean_dec_ref(v_x_1173_);
    v_r_1179_ = crate::leanh::lean_box((v_res_1178_) as usize);
    return v_r_1179_;
}
pub unsafe fn l_Std_ExtHashSet_ofList___redArg(
    mut v_inst_1203_: *mut crate::leanh::LeanObject,
    mut v_inst_1204_: *mut crate::leanh::LeanObject,
    mut v_l_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1206_ = l_Std_ExtHashSet_ofList___redArg___closed__11;
    v___x_1207_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__1,
    );
    v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_1206_,
        v_inst_1203_,
        v_inst_1204_,
        v___x_1207_,
        v_l_1205_,
    );
    return v___x_1208_;
}
pub unsafe fn l_Std_ExtHashSet_ofList(
    mut v_00_u03b1_1209_: *mut crate::leanh::LeanObject,
    mut v_inst_1210_: *mut crate::leanh::LeanObject,
    mut v_inst_1211_: *mut crate::leanh::LeanObject,
    mut v_l_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1213_ = l_Std_ExtHashSet_ofList___redArg___closed__11;
    v___x_1214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__1,
    );
    v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_1213_,
        v_inst_1210_,
        v_inst_1211_,
        v___x_1214_,
        v_l_1212_,
    );
    return v___x_1215_;
}
pub unsafe fn l_Std_ExtHashSet_filter___redArg___lam__0(
    mut v_f_1216_: *mut crate::leanh::LeanObject,
    mut v_a_1217_: *mut crate::leanh::LeanObject,
    mut v_x_1218_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: u8 = 0;
    v___x_1219_ = crate::leanh::lean_apply_1(v_f_1216_, v_a_1217_);
    v___x_1220_ = (crate::leanh::lean_unbox(v___x_1219_) as u8);
    return v___x_1220_;
}
pub unsafe fn l_Std_ExtHashSet_filter___redArg___lam__0___boxed(
    mut v_f_1221_: *mut crate::leanh::LeanObject,
    mut v_a_1222_: *mut crate::leanh::LeanObject,
    mut v_x_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: u8 = 0;
    let mut v_r_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Std_ExtHashSet_filter___redArg___lam__0(v_f_1221_, v_a_1222_, v_x_1223_);
    v_r_1225_ = crate::leanh::lean_box((v_res_1224_) as usize);
    return v_r_1225_;
}
pub unsafe fn l_Std_ExtHashSet_filter___redArg(
    mut v_f_1226_: *mut crate::leanh::LeanObject,
    mut v_m_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1228_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1228_, 0, v_f_1226_);
    v___x_1229_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1228_, v_m_1227_);
    return v___x_1229_;
}
pub unsafe fn l_Std_ExtHashSet_filter(
    mut v_00_u03b1_1230_: *mut crate::leanh::LeanObject,
    mut v_x_1231_: *mut crate::leanh::LeanObject,
    mut v_x_1232_: *mut crate::leanh::LeanObject,
    mut v_inst_1233_: *mut crate::leanh::LeanObject,
    mut v_inst_1234_: *mut crate::leanh::LeanObject,
    mut v_f_1235_: *mut crate::leanh::LeanObject,
    mut v_m_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1237_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_filter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1237_, 0, v_f_1235_);
    v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1237_, v_m_1236_);
    return v___x_1238_;
}
pub unsafe fn l_Std_ExtHashSet_filter___boxed(
    mut v_00_u03b1_1239_: *mut crate::leanh::LeanObject,
    mut v_x_1240_: *mut crate::leanh::LeanObject,
    mut v_x_1241_: *mut crate::leanh::LeanObject,
    mut v_inst_1242_: *mut crate::leanh::LeanObject,
    mut v_inst_1243_: *mut crate::leanh::LeanObject,
    mut v_f_1244_: *mut crate::leanh::LeanObject,
    mut v_m_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l_Std_ExtHashSet_filter(
        v_00_u03b1_1239_,
        v_x_1240_,
        v_x_1241_,
        v_inst_1242_,
        v_inst_1243_,
        v_f_1244_,
        v_m_1245_,
    );
    crate::leanh::lean_dec_ref(v_x_1241_);
    crate::leanh::lean_dec_ref(v_x_1240_);
    return v_res_1246_;
}
pub unsafe fn l_Std_ExtHashSet_insertMany___redArg___lam__0(
    mut v_x_1247_: *mut crate::leanh::LeanObject,
    mut v_x_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
    mut v_____s_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = crate::leanh::lean_box(0);
    v_m_1252_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1247_,
        v_x_1248_,
        v_____s_1250_,
        v_a_1249_,
        v___x_1251_,
    );
    v___x_1253_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1253_, 0, v_m_1252_);
    return v___x_1253_;
}
pub unsafe fn l_Std_ExtHashSet_insertMany___redArg(
    mut v_x_1254_: *mut crate::leanh::LeanObject,
    mut v_x_1255_: *mut crate::leanh::LeanObject,
    mut v_inst_1256_: *mut crate::leanh::LeanObject,
    mut v_m_1257_: *mut crate::leanh::LeanObject,
    mut v_l_1258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1259_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1259_, 0, v_x_1254_);
    crate::leanh::lean_closure_set(v___f_1259_, 1, v_x_1255_);
    v___x_1260_ = crate::leanh::lean_apply_4(
        v_inst_1256_,
        crate::leanh::lean_box(0),
        v_l_1258_,
        v_m_1257_,
        v___f_1259_,
    );
    return v___x_1260_;
}
pub unsafe fn l_Std_ExtHashSet_insertMany(
    mut v_00_u03b1_1261_: *mut crate::leanh::LeanObject,
    mut v_x_1262_: *mut crate::leanh::LeanObject,
    mut v_x_1263_: *mut crate::leanh::LeanObject,
    mut v_inst_1264_: *mut crate::leanh::LeanObject,
    mut v_inst_1265_: *mut crate::leanh::LeanObject,
    mut v_00_u03c1_1266_: *mut crate::leanh::LeanObject,
    mut v_inst_1267_: *mut crate::leanh::LeanObject,
    mut v_m_1268_: *mut crate::leanh::LeanObject,
    mut v_l_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1270_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_insertMany___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1270_, 0, v_x_1262_);
    crate::leanh::lean_closure_set(v___f_1270_, 1, v_x_1263_);
    v___x_1271_ = crate::leanh::lean_apply_4(
        v_inst_1267_,
        crate::leanh::lean_box(0),
        v_l_1269_,
        v_m_1268_,
        v___f_1270_,
    );
    return v___x_1271_;
}
pub unsafe fn l_Std_ExtHashSet_union___redArg___lam__0(
    mut v_x_1272_: *mut crate::leanh::LeanObject,
    mut v_x_1273_: *mut crate::leanh::LeanObject,
    mut v_a_1274_: *mut crate::leanh::LeanObject,
    mut v_b_1275_: *mut crate::leanh::LeanObject,
    mut v_acc_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_1277_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
        v_x_1272_,
        v_x_1273_,
        v_acc_1276_,
        v_a_1274_,
        v_b_1275_,
    );
    v___x_1278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1278_, 0, v_r_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Std_ExtHashSet_union___redArg___lam__1(
    mut v___x_1279_: *mut crate::leanh::LeanObject,
    mut v___f_1280_: *mut crate::leanh::LeanObject,
    mut v_a_1281_: *mut crate::leanh::LeanObject,
    mut v_x_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1284_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), crate::leanh::lean_box(0), v___x_1279_, v___f_1280_, v_a_1281_, v___y_1283_);
    return v___x_1284_;
}
pub unsafe fn l_Std_ExtHashSet_union___redArg(
    mut v_x_1287_: *mut crate::leanh::LeanObject,
    mut v_x_1288_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1289_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: u8 = 0;
    v_size_1291_ = crate::leanh::lean_ctor_get(v_m_u2081_1289_, 0);
    v_buckets_1292_ = crate::leanh::lean_ctor_get(v_m_u2081_1289_, 1);
    v_size_1293_ = crate::leanh::lean_ctor_get(v_m_u2082_1290_, 0);
    v___x_1294_ = lean_nat_dec_le(v_size_1291_, v_size_1293_);
    if v___x_1294_ == 0 {
        let mut v___f_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1295_ = l_Std_ExtHashSet_union___redArg___closed__0;
        v___x_1296_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_1295_,
            v_x_1287_,
            v_x_1288_,
            v_m_u2081_1289_,
            v_m_u2082_1290_,
        );
        return v___x_1296_;
    } else {
        let mut v___f_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1300_: usize = 0;
        let mut v___x_1301_: usize = 0;
        let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_1292_);
        crate::leanh::lean_dec(v_m_u2081_1289_);
        v___f_1297_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashSet_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1297_, 0, v_x_1287_);
        crate::leanh::lean_closure_set(v___f_1297_, 1, v_x_1288_);
        v___x_1298_ = l_Std_ExtHashSet_ofList___redArg___closed__9;
        v___f_1299_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashSet_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1299_, 0, v___x_1298_);
        crate::leanh::lean_closure_set(v___f_1299_, 1, v___f_1297_);
        v_sz_1300_ = lean_array_size(v_buckets_1292_);
        v___x_1301_ = 0usize;
        v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1298_,
            v_buckets_1292_,
            v___f_1299_,
            v_sz_1300_,
            v___x_1301_,
            v_m_u2082_1290_,
        );
        return v___x_1302_;
    }
}
pub unsafe fn l_Std_ExtHashSet_union(
    mut v_00_u03b1_1303_: *mut crate::leanh::LeanObject,
    mut v_x_1304_: *mut crate::leanh::LeanObject,
    mut v_x_1305_: *mut crate::leanh::LeanObject,
    mut v_inst_1306_: *mut crate::leanh::LeanObject,
    mut v_inst_1307_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1308_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: u8 = 0;
    v_size_1310_ = crate::leanh::lean_ctor_get(v_m_u2081_1308_, 0);
    v_buckets_1311_ = crate::leanh::lean_ctor_get(v_m_u2081_1308_, 1);
    v_size_1312_ = crate::leanh::lean_ctor_get(v_m_u2082_1309_, 0);
    v___x_1313_ = lean_nat_dec_le(v_size_1310_, v_size_1312_);
    if v___x_1313_ == 0 {
        let mut v___f_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1314_ = l_Std_ExtHashSet_union___redArg___closed__0;
        v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(
            v___f_1314_,
            v_x_1304_,
            v_x_1305_,
            v_m_u2081_1308_,
            v_m_u2082_1309_,
        );
        return v___x_1315_;
    } else {
        let mut v___f_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_1319_: usize = 0;
        let mut v___x_1320_: usize = 0;
        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_buckets_1311_);
        crate::leanh::lean_dec(v_m_u2081_1308_);
        v___f_1316_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashSet_union___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1316_, 0, v_x_1304_);
        crate::leanh::lean_closure_set(v___f_1316_, 1, v_x_1305_);
        v___x_1317_ = l_Std_ExtHashSet_ofList___redArg___closed__9;
        v___f_1318_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashSet_union___redArg___lam__1 as *mut core::ffi::c_void,
            5,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1318_, 0, v___x_1317_);
        crate::leanh::lean_closure_set(v___f_1318_, 1, v___f_1316_);
        v_sz_1319_ = lean_array_size(v_buckets_1311_);
        v___x_1320_ = 0usize;
        v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1317_,
            v_buckets_1311_,
            v___f_1318_,
            v_sz_1319_,
            v___x_1320_,
            v_m_u2082_1309_,
        );
        return v___x_1321_;
    }
}
pub unsafe fn l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1322_: *mut crate::leanh::LeanObject,
    mut v_x_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1324_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashSet_union as *mut core::ffi::c_void, 7, 5);
    crate::leanh::lean_closure_set(v___x_1324_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1324_, 1, v_x_1322_);
    crate::leanh::lean_closure_set(v___x_1324_, 2, v_x_1323_);
    crate::leanh::lean_closure_set(v___x_1324_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1324_, 4, crate::leanh::lean_box(0));
    return v___x_1324_;
}
pub unsafe fn l_Std_ExtHashSet_instUnionOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1325_: *mut crate::leanh::LeanObject,
    mut v_x_1326_: *mut crate::leanh::LeanObject,
    mut v_x_1327_: *mut crate::leanh::LeanObject,
    mut v_inst_1328_: *mut crate::leanh::LeanObject,
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1330_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashSet_union as *mut core::ffi::c_void, 7, 5);
    crate::leanh::lean_closure_set(v___x_1330_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1330_, 1, v_x_1326_);
    crate::leanh::lean_closure_set(v___x_1330_, 2, v_x_1327_);
    crate::leanh::lean_closure_set(v___x_1330_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1330_, 4, crate::leanh::lean_box(0));
    return v___x_1330_;
}
pub unsafe fn _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = crate::leanh::lean_alloc_closure(
        l_instDecidableEqPUnit___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1332_ = crate::leanh::lean_alloc_closure(
        l_instBEqOfDecidableEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1332_, 0, v___x_1331_);
    return v___f_1332_;
}
pub unsafe fn l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(
    mut v_x_1333_: *mut crate::leanh::LeanObject,
    mut v_x_1334_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1335_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1336_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: u8 = 0;
    v___f_1337_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0,
    );
    v___x_1338_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_x_1333_,
        v_x_1334_,
        v___f_1337_,
        v_m_u2081_1335_,
        v_m_u2082_1336_,
    );
    return v___x_1338_;
}
pub unsafe fn l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed(
    mut v_x_1339_: *mut crate::leanh::LeanObject,
    mut v_x_1340_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1341_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1343_: u8 = 0;
    let mut v_r_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1343_ = l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0(
        v_x_1339_,
        v_x_1340_,
        v_m_u2081_1341_,
        v_m_u2082_1342_,
    );
    v_r_1344_ = crate::leanh::lean_box((v_res_1343_) as usize);
    return v_r_1344_;
}
pub unsafe fn l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1345_: *mut crate::leanh::LeanObject,
    mut v_x_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1347_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1347_, 0, v_x_1345_);
    crate::leanh::lean_closure_set(v___f_1347_, 1, v_x_1346_);
    return v___f_1347_;
}
pub unsafe fn l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1348_: *mut crate::leanh::LeanObject,
    mut v_x_1349_: *mut crate::leanh::LeanObject,
    mut v_x_1350_: *mut crate::leanh::LeanObject,
    mut v_inst_1351_: *mut crate::leanh::LeanObject,
    mut v_inst_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1353_ = crate::leanh::lean_alloc_closure(
        l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1353_, 0, v_x_1349_);
    crate::leanh::lean_closure_set(v___f_1353_, 1, v_x_1350_);
    return v___f_1353_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(
    mut v_inst_1354_: *mut crate::leanh::LeanObject,
    mut v_inst_1355_: *mut crate::leanh::LeanObject,
    mut v_x_1356_: *mut crate::leanh::LeanObject,
    mut v_x_1357_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: u8 = 0;
    v___f_1358_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0_once
        ),
        _init_l_Std_ExtHashSet_instBEqOfEquivBEqOfLawfulHashable___redArg___lam__0___closed__0,
    );
    v___x_1359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(
        v_inst_1354_,
        v_inst_1355_,
        v___f_1358_,
        v_x_1356_,
        v_x_1357_,
    );
    return v___x_1359_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg___boxed(
    mut v_inst_1360_: *mut crate::leanh::LeanObject,
    mut v_inst_1361_: *mut crate::leanh::LeanObject,
    mut v_x_1362_: *mut crate::leanh::LeanObject,
    mut v_x_1363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1364_: u8 = 0;
    let mut v_r_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(
        v_inst_1360_,
        v_inst_1361_,
        v_x_1362_,
        v_x_1363_,
    );
    v_r_1365_ = crate::leanh::lean_box((v_res_1364_) as usize);
    return v_r_1365_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(
    mut v_00_u03b1_1366_: *mut crate::leanh::LeanObject,
    mut v_inst_1367_: *mut crate::leanh::LeanObject,
    mut v_inst_1368_: *mut crate::leanh::LeanObject,
    mut v_inst_1369_: *mut crate::leanh::LeanObject,
    mut v_x_1370_: *mut crate::leanh::LeanObject,
    mut v_x_1371_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1372_: u8 = 0;
    v___x_1372_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___redArg(
        v_inst_1367_,
        v_inst_1369_,
        v_x_1370_,
        v_x_1371_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Std_ExtHashSet_instDecidableEqOfLawfulBEq___boxed(
    mut v_00_u03b1_1373_: *mut crate::leanh::LeanObject,
    mut v_inst_1374_: *mut crate::leanh::LeanObject,
    mut v_inst_1375_: *mut crate::leanh::LeanObject,
    mut v_inst_1376_: *mut crate::leanh::LeanObject,
    mut v_x_1377_: *mut crate::leanh::LeanObject,
    mut v_x_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1379_: u8 = 0;
    let mut v_r_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1379_ = l_Std_ExtHashSet_instDecidableEqOfLawfulBEq(
        v_00_u03b1_1373_,
        v_inst_1374_,
        v_inst_1375_,
        v_inst_1376_,
        v_x_1377_,
        v_x_1378_,
    );
    v_r_1380_ = crate::leanh::lean_box((v_res_1379_) as usize);
    return v_r_1380_;
}
pub unsafe fn l_Std_ExtHashSet_inter___redArg(
    mut v_x_1381_: *mut crate::leanh::LeanObject,
    mut v_x_1382_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1383_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1385_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_1381_,
        v_x_1382_,
        v_m_u2081_1383_,
        v_m_u2082_1384_,
    );
    return v___x_1385_;
}
pub unsafe fn l_Std_ExtHashSet_inter(
    mut v_00_u03b1_1386_: *mut crate::leanh::LeanObject,
    mut v_x_1387_: *mut crate::leanh::LeanObject,
    mut v_x_1388_: *mut crate::leanh::LeanObject,
    mut v_inst_1389_: *mut crate::leanh::LeanObject,
    mut v_inst_1390_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1391_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(
        v_x_1387_,
        v_x_1388_,
        v_m_u2081_1391_,
        v_m_u2082_1392_,
    );
    return v___x_1393_;
}
pub unsafe fn l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1394_: *mut crate::leanh::LeanObject,
    mut v_x_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashSet_inter as *mut core::ffi::c_void, 7, 5);
    crate::leanh::lean_closure_set(v___x_1396_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1396_, 1, v_x_1394_);
    crate::leanh::lean_closure_set(v___x_1396_, 2, v_x_1395_);
    crate::leanh::lean_closure_set(v___x_1396_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1396_, 4, crate::leanh::lean_box(0));
    return v___x_1396_;
}
pub unsafe fn l_Std_ExtHashSet_instInterOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1397_: *mut crate::leanh::LeanObject,
    mut v_x_1398_: *mut crate::leanh::LeanObject,
    mut v_x_1399_: *mut crate::leanh::LeanObject,
    mut v_inst_1400_: *mut crate::leanh::LeanObject,
    mut v_inst_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashSet_inter as *mut core::ffi::c_void, 7, 5);
    crate::leanh::lean_closure_set(v___x_1402_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1402_, 1, v_x_1398_);
    crate::leanh::lean_closure_set(v___x_1402_, 2, v_x_1399_);
    crate::leanh::lean_closure_set(v___x_1402_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1402_, 4, crate::leanh::lean_box(0));
    return v___x_1402_;
}
pub unsafe fn l_Std_ExtHashSet_diff___redArg___lam__0(
    mut v_x_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1405_: *mut crate::leanh::LeanObject,
    mut v___x_1406_: u8,
    mut v_k_1407_: *mut crate::leanh::LeanObject,
    mut v_x_1408_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1409_: u8 = 0;
    v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        v_x_1403_,
        v_x_1404_,
        v_m_u2082_1405_,
        v_k_1407_,
    );
    if v___x_1409_ == 0 {
        return v___x_1406_;
    } else {
        let mut v___x_1410_: u8 = 0;
        v___x_1410_ = 0;
        return v___x_1410_;
    }
}
pub unsafe fn l_Std_ExtHashSet_diff___redArg___lam__0___boxed(
    mut v_x_1411_: *mut crate::leanh::LeanObject,
    mut v_x_1412_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1413_: *mut crate::leanh::LeanObject,
    mut v___x_1414_: *mut crate::leanh::LeanObject,
    mut v_k_1415_: *mut crate::leanh::LeanObject,
    mut v_x_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_109__boxed_1417_: u8 = 0;
    let mut v_res_1418_: u8 = 0;
    let mut v_r_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_109__boxed_1417_ = (crate::leanh::lean_unbox(v___x_1414_) as u8);
    v_res_1418_ = l_Std_ExtHashSet_diff___redArg___lam__0(
        v_x_1411_,
        v_x_1412_,
        v_m_u2082_1413_,
        v___x_109__boxed_1417_,
        v_k_1415_,
        v_x_1416_,
    );
    crate::leanh::lean_dec(v_m_u2082_1413_);
    v_r_1419_ = crate::leanh::lean_box((v_res_1418_) as usize);
    return v_r_1419_;
}
pub unsafe fn l_Std_ExtHashSet_diff___redArg(
    mut v_x_1420_: *mut crate::leanh::LeanObject,
    mut v_x_1421_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1422_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    v_size_1424_ = crate::leanh::lean_ctor_get(v_m_u2081_1422_, 0);
    v_size_1425_ = crate::leanh::lean_ctor_get(v_m_u2082_1423_, 0);
    v___x_1426_ = lean_nat_dec_le(v_size_1424_, v_size_1425_);
    if v___x_1426_ == 0 {
        let mut v___f_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1427_ = l_Std_ExtHashSet_union___redArg___closed__0;
        v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_1427_,
            v_x_1420_,
            v_x_1421_,
            v_m_u2081_1422_,
            v_m_u2082_1423_,
        );
        return v___x_1428_;
    } else {
        let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1429_ = crate::leanh::lean_box((v___x_1426_) as usize);
        v___f_1430_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashSet_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1430_, 0, v_x_1420_);
        crate::leanh::lean_closure_set(v___f_1430_, 1, v_x_1421_);
        crate::leanh::lean_closure_set(v___f_1430_, 2, v_m_u2082_1423_);
        crate::leanh::lean_closure_set(v___f_1430_, 3, v___x_1429_);
        v___x_1431_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1430_, v_m_u2081_1422_);
        return v___x_1431_;
    }
}
pub unsafe fn l_Std_ExtHashSet_diff(
    mut v_00_u03b1_1432_: *mut crate::leanh::LeanObject,
    mut v_x_1433_: *mut crate::leanh::LeanObject,
    mut v_x_1434_: *mut crate::leanh::LeanObject,
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_inst_1436_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1437_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    v_size_1439_ = crate::leanh::lean_ctor_get(v_m_u2081_1437_, 0);
    v_size_1440_ = crate::leanh::lean_ctor_get(v_m_u2082_1438_, 0);
    v___x_1441_ = lean_nat_dec_le(v_size_1439_, v_size_1440_);
    if v___x_1441_ == 0 {
        let mut v___f_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1442_ = l_Std_ExtHashSet_union___redArg___closed__0;
        v___x_1443_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(
            v___f_1442_,
            v_x_1433_,
            v_x_1434_,
            v_m_u2081_1437_,
            v_m_u2082_1438_,
        );
        return v___x_1443_;
    } else {
        let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1444_ = crate::leanh::lean_box((v___x_1441_) as usize);
        v___f_1445_ = crate::leanh::lean_alloc_closure(
            l_Std_ExtHashSet_diff___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            4,
        );
        crate::leanh::lean_closure_set(v___f_1445_, 0, v_x_1433_);
        crate::leanh::lean_closure_set(v___f_1445_, 1, v_x_1434_);
        crate::leanh::lean_closure_set(v___f_1445_, 2, v_m_u2082_1438_);
        crate::leanh::lean_closure_set(v___f_1445_, 3, v___x_1444_);
        v___x_1446_ =
            l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1445_, v_m_u2081_1437_);
        return v___x_1446_;
    }
}
pub unsafe fn l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable___redArg(
    mut v_x_1447_: *mut crate::leanh::LeanObject,
    mut v_x_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1449_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashSet_diff as *mut core::ffi::c_void, 7, 5);
    crate::leanh::lean_closure_set(v___x_1449_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1449_, 1, v_x_1447_);
    crate::leanh::lean_closure_set(v___x_1449_, 2, v_x_1448_);
    crate::leanh::lean_closure_set(v___x_1449_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1449_, 4, crate::leanh::lean_box(0));
    return v___x_1449_;
}
pub unsafe fn l_Std_ExtHashSet_instSDiffOfEquivBEqOfLawfulHashable(
    mut v_00_u03b1_1450_: *mut crate::leanh::LeanObject,
    mut v_x_1451_: *mut crate::leanh::LeanObject,
    mut v_x_1452_: *mut crate::leanh::LeanObject,
    mut v_inst_1453_: *mut crate::leanh::LeanObject,
    mut v_inst_1454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ =
        crate::leanh::lean_alloc_closure(l_Std_ExtHashSet_diff as *mut core::ffi::c_void, 7, 5);
    crate::leanh::lean_closure_set(v___x_1455_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1455_, 1, v_x_1451_);
    crate::leanh::lean_closure_set(v___x_1455_, 2, v_x_1452_);
    crate::leanh::lean_closure_set(v___x_1455_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1455_, 4, crate::leanh::lean_box(0));
    return v___x_1455_;
}
pub unsafe fn l_Std_ExtHashSet_ofArray___redArg(
    mut v_inst_1460_: *mut crate::leanh::LeanObject,
    mut v_inst_1461_: *mut crate::leanh::LeanObject,
    mut v_l_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1463_ = l_Std_ExtHashSet_ofArray___redArg___closed__1;
    v___x_1464_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__1,
    );
    v___x_1465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_1463_,
        v_inst_1460_,
        v_inst_1461_,
        v___x_1464_,
        v_l_1462_,
    );
    return v___x_1465_;
}
pub unsafe fn l_Std_ExtHashSet_ofArray(
    mut v_00_u03b1_1466_: *mut crate::leanh::LeanObject,
    mut v_inst_1467_: *mut crate::leanh::LeanObject,
    mut v_inst_1468_: *mut crate::leanh::LeanObject,
    mut v_l_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1470_ = l_Std_ExtHashSet_ofArray___redArg___closed__1;
    v___x_1471_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1),
        core::ptr::addr_of_mut!(l_Std_ExtHashSet_instEmptyCollection___closed__1_once),
        _init_l_Std_ExtHashSet_instEmptyCollection___closed__1,
    );
    v___x_1472_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(
        v___f_1470_,
        v_inst_1467_,
        v_inst_1468_,
        v___x_1471_,
        v_l_1469_,
    );
    return v___x_1472_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_ExtHashSet_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_ExtHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_ExtHashSet_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_ExtHashSet_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_ExtHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_ExtHashSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_ExtHashSet_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_ExtHashSet_Basic(builtin);
}
