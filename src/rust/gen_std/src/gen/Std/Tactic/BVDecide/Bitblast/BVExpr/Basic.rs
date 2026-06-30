// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
// Imports: Init.Data.Hashable Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic Init.Data.RArray Init.Data.ToString.Macro Init.Data.BitVec.Lemmas Init.Omega
use crate::ffi::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_land, lean_nat_lor,
    lean_nat_lxor, lean_nat_mod, lean_nat_shiftr, lean_nat_to_int, lean_ptr_addr,
    lean_string_append, lean_string_length, lean_uint64_dec_eq, lean_uint64_mix_hash,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::r#gen::Init::Data::BitVec::Basic::{
    l_BitVec_append___redArg, l_BitVec_clz, l_BitVec_cpop, l_BitVec_extractLsb_x27___redArg,
    l_BitVec_hash, l_BitVec_mul, l_BitVec_not, l_BitVec_replicate, l_BitVec_repr, l_BitVec_reverse,
    l_BitVec_rotateLeft, l_BitVec_rotateRight, l_BitVec_setWidth, l_BitVec_shiftLeft,
    l_BitVec_sshiftRight,
};
use crate::r#gen::Init::Data::BitVec::BasicAux::l_BitVec_add;
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::l_Nat_testBit;
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, l_Lean_RArray_getImpl___redArg,
    runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BoolExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic,
    l_Std_Tactic_BVDecide_BoolExpr_eval___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic,
};
pub static l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_instHashableBVBit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_instHashableBVBit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instHashableBVBit___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0_value:
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
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1_value:
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
    m_data: [118, 97, 114, 0],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4_value:
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
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
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
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [119, 0],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value:
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
    m_data: [105, 100, 120, 0],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value:
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
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__15_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instReprBVBit___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Tactic_BVDecide_instReprBVBit_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_instReprBVBit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_instReprBVBit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instReprBVBit___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [91, 0],
};
static mut l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_instToStringBVBit___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_instToStringBVBit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_instToStringBVBit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instToStringBVBit___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Tactic_BVDecide_instInhabitedBVBit: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_instHashableBVBinOp: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instHashableBVBinOp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0_value:
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
    m_data: [38, 38, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1_value:
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
    m_data: [124, 124, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [94, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [43, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [42, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [47, 225, 181, 164, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [37, 225, 181, 164, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_BVBinOp_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_BVBinOp_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinOp_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_instHashableBVUnOp: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_instHashableBVUnOp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0_value: leanh::LeanStringObject<
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
    m_data: [126, 0],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 111, 116, 76, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 111, 116, 82, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3_value: leanh::LeanStringObject<
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
    m_data: [62, 62, 97, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 101, 118, 0],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [99, 108, 122, 0],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6_value: leanh::LeanStringObject<
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
    m_data: [99, 112, 111, 112, 0],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_BVUnOp_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_BVUnOp_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVUnOp_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__0_value: leanh::LeanStringObject<
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
    m_data: [44, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__1_value: leanh::LeanStringObject<
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
    m_data: [40, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__2_value: leanh::LeanStringObject<
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
    m_data: [32, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__3_value: leanh::LeanStringObject<
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
    m_data: [41, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__4_value: leanh::LeanStringObject<
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
    m_data: [32, 43, 43, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__5_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [40, 114, 101, 112, 108, 105, 99, 97, 116, 101, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__6_value: leanh::LeanStringObject<
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
    m_data: [32, 60, 60, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__7_value: leanh::LeanStringObject<
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
    m_data: [32, 62, 62, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_toString___closed__8_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 62, 62, 97, 32, 0],
};
static mut l_Std_Tactic_BVDecide_BVExpr_toString___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_toString___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0_value:
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
    m_data: [61, 61, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1_value:
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
    m_data: [60, 117, 0],
};
static mut l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_BVBinPred_toString___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_BVBinPred_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVBinPred_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_BVPred_instToString___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_BVPred_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_BVPred_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVPred_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_BVPred_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVPred_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_instHashableBVBit_hash(
    mut v_x_1769_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_var_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: u64 = 0;
    let mut v___x_1774_: u64 = 0;
    let mut v___x_1775_: u64 = 0;
    let mut v___x_1776_: u64 = 0;
    let mut v___x_1777_: u64 = 0;
    let mut v___x_1778_: u64 = 0;
    let mut v___x_1779_: u64 = 0;
    v_var_1770_ = leanh::lean_ctor_get(v_x_1769_, 0);
    v_w_1771_ = leanh::lean_ctor_get(v_x_1769_, 1);
    v_idx_1772_ = leanh::lean_ctor_get(v_x_1769_, 2);
    v___x_1773_ = 0u64;
    v___x_1774_ = lean_uint64_of_nat(v_var_1770_);
    v___x_1775_ = lean_uint64_mix_hash(v___x_1773_, v___x_1774_);
    v___x_1776_ = lean_uint64_of_nat(v_w_1771_);
    v___x_1777_ = lean_uint64_mix_hash(v___x_1775_, v___x_1776_);
    v___x_1778_ = lean_uint64_of_nat(v_idx_1772_);
    v___x_1779_ = lean_uint64_mix_hash(v___x_1777_, v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instHashableBVBit_hash___boxed(
    mut v_x_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1781_: u64 = 0;
    let mut v_r_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1781_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_x_1780_);
    leanh::lean_dec_ref(v_x_1780_);
    v_r_1782_ = leanh::lean_box_uint64(v_res_1781_);
    return v_r_1782_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(
    mut v_x_1785_: *mut leanh::LeanObject,
    mut v_x_1786_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_var_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_var_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    v_var_1787_ = leanh::lean_ctor_get(v_x_1785_, 0);
    v_w_1788_ = leanh::lean_ctor_get(v_x_1785_, 1);
    v_idx_1789_ = leanh::lean_ctor_get(v_x_1785_, 2);
    v_var_1790_ = leanh::lean_ctor_get(v_x_1786_, 0);
    v_w_1791_ = leanh::lean_ctor_get(v_x_1786_, 1);
    v_idx_1792_ = leanh::lean_ctor_get(v_x_1786_, 2);
    v___x_1793_ = lean_nat_dec_eq(v_var_1787_, v_var_1790_);
    if v___x_1793_ == 0 {
        return v___x_1793_;
    } else {
        let mut v___x_1794_: u8 = 0;
        v___x_1794_ = lean_nat_dec_eq(v_w_1788_, v_w_1791_);
        if v___x_1794_ == 0 {
            return v___x_1794_;
        } else {
            let mut v___x_1795_: u8 = 0;
            v___x_1795_ = lean_nat_dec_eq(v_idx_1789_, v_idx_1792_);
            return v___x_1795_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq___boxed(
    mut v_x_1796_: *mut leanh::LeanObject,
    mut v_x_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1798_: u8 = 0;
    let mut v_r_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_x_1796_, v_x_1797_);
    leanh::lean_dec_ref(v_x_1797_);
    leanh::lean_dec_ref(v_x_1796_);
    v_r_1799_ = leanh::lean_box((v_res_1798_) as usize);
    return v_r_1799_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVBit(
    mut v_x_1800_: *mut leanh::LeanObject,
    mut v_x_1801_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1802_: u8 = 0;
    v___x_1802_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_x_1800_, v_x_1801_);
    return v___x_1802_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(
    mut v_x_1803_: *mut leanh::LeanObject,
    mut v_x_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1805_: u8 = 0;
    let mut v_r_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1805_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit(v_x_1803_, v_x_1804_);
    leanh::lean_dec_ref(v_x_1804_);
    leanh::lean_dec_ref(v_x_1803_);
    v_r_1806_ = leanh::lean_box((v_res_1805_) as usize);
    return v_r_1806_;
}
pub unsafe fn l_Nat_cast___at___00Std_Tactic_BVDecide_instReprBVBit_repr_spec__0(
    mut v_a_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1808_ = lean_nat_to_int(v_a_1807_);
    return v___x_1808_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = leanh::lean_unsigned_to_nat(7);
    v___x_1823_ = lean_nat_to_int(v___x_1822_);
    return v___x_1823_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = leanh::lean_unsigned_to_nat(5);
    v___x_1831_ = lean_nat_to_int(v___x_1830_);
    return v___x_1831_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__0;
    v___x_1837_ = lean_string_length(v___x_1836_);
    return v___x_1837_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16_once
        ),
        _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__16,
    );
    v___x_1839_ = lean_nat_to_int(v___x_1838_);
    return v___x_1839_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(
    mut v_x_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_var_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: u8 = 0;
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_var_1845_ = leanh::lean_ctor_get(v_x_1844_, 0);
    leanh::lean_inc(v_var_1845_);
    v_w_1846_ = leanh::lean_ctor_get(v_x_1844_, 1);
    leanh::lean_inc(v_w_1846_);
    v_idx_1847_ = leanh::lean_ctor_get(v_x_1844_, 2);
    leanh::lean_inc(v_idx_1847_);
    leanh::lean_dec_ref(v_x_1844_);
    v___x_1848_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__5;
    v___x_1849_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__6;
    v___x_1850_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7_once),
        _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__7,
    );
    v___x_1851_ = l_Nat_reprFast(v_var_1845_);
    v___x_1852_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1852_, 0, v___x_1851_);
    v___x_1853_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1853_, 0, v___x_1850_);
    leanh::lean_ctor_set(v___x_1853_, 1, v___x_1852_);
    v___x_1854_ = 0;
    v___x_1855_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1855_, 0, v___x_1853_);
    leanh::lean_ctor_set_uint8(
        v___x_1855_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1854_,
    );
    v___x_1856_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1856_, 0, v___x_1849_);
    leanh::lean_ctor_set(v___x_1856_, 1, v___x_1855_);
    v___x_1857_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__9;
    v___x_1858_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1858_, 0, v___x_1856_);
    leanh::lean_ctor_set(v___x_1858_, 1, v___x_1857_);
    v___x_1859_ = leanh::lean_box(1);
    v___x_1860_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1860_, 0, v___x_1858_);
    leanh::lean_ctor_set(v___x_1860_, 1, v___x_1859_);
    v___x_1861_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__11;
    v___x_1862_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1862_, 0, v___x_1860_);
    leanh::lean_ctor_set(v___x_1862_, 1, v___x_1861_);
    v___x_1863_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v___x_1862_);
    leanh::lean_ctor_set(v___x_1863_, 1, v___x_1848_);
    v___x_1864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12_once
        ),
        _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__12,
    );
    v___x_1865_ = l_Nat_reprFast(v_w_1846_);
    v___x_1866_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1866_, 0, v___x_1865_);
    v___x_1867_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1867_, 0, v___x_1864_);
    leanh::lean_ctor_set(v___x_1867_, 1, v___x_1866_);
    v___x_1868_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1868_, 0, v___x_1867_);
    leanh::lean_ctor_set_uint8(
        v___x_1868_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1854_,
    );
    v___x_1869_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1869_, 0, v___x_1863_);
    leanh::lean_ctor_set(v___x_1869_, 1, v___x_1868_);
    v___x_1870_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1870_, 0, v___x_1869_);
    leanh::lean_ctor_set(v___x_1870_, 1, v___x_1857_);
    v___x_1871_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1871_, 0, v___x_1870_);
    leanh::lean_ctor_set(v___x_1871_, 1, v___x_1859_);
    v___x_1872_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__14;
    v___x_1873_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1873_, 0, v___x_1871_);
    leanh::lean_ctor_set(v___x_1873_, 1, v___x_1872_);
    v___x_1874_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1874_, 0, v___x_1873_);
    leanh::lean_ctor_set(v___x_1874_, 1, v___x_1848_);
    v___x_1875_ = l_Nat_reprFast(v_idx_1847_);
    v___x_1876_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1876_, 0, v___x_1875_);
    v___x_1877_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1877_, 0, v___x_1850_);
    leanh::lean_ctor_set(v___x_1877_, 1, v___x_1876_);
    v___x_1878_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1878_, 0, v___x_1877_);
    leanh::lean_ctor_set_uint8(
        v___x_1878_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1854_,
    );
    v___x_1879_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1879_, 0, v___x_1874_);
    leanh::lean_ctor_set(v___x_1879_, 1, v___x_1878_);
    v___x_1880_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17_once
        ),
        _init_l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__17,
    );
    v___x_1881_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__18;
    v___x_1882_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1882_, 0, v___x_1881_);
    leanh::lean_ctor_set(v___x_1882_, 1, v___x_1879_);
    v___x_1883_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__19;
    v___x_1884_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1884_, 0, v___x_1882_);
    leanh::lean_ctor_set(v___x_1884_, 1, v___x_1883_);
    v___x_1885_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1885_, 0, v___x_1880_);
    leanh::lean_ctor_set(v___x_1885_, 1, v___x_1884_);
    v___x_1886_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1886_, 0, v___x_1885_);
    leanh::lean_ctor_set_uint8(
        v___x_1886_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1854_,
    );
    return v___x_1886_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instReprBVBit_repr(
    mut v_x_1887_: *mut leanh::LeanObject,
    mut v_prec_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg(v_x_1887_);
    return v___x_1889_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instReprBVBit_repr___boxed(
    mut v_x_1890_: *mut leanh::LeanObject,
    mut v_prec_1891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1892_ = l_Std_Tactic_BVDecide_instReprBVBit_repr(v_x_1890_, v_prec_1891_);
    leanh::lean_dec(v_prec_1891_);
    return v_res_1892_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(
    mut v_b_1898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_var_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_var_1899_ = leanh::lean_ctor_get(v_b_1898_, 0);
    leanh::lean_inc(v_var_1899_);
    v_idx_1900_ = leanh::lean_ctor_get(v_b_1898_, 2);
    leanh::lean_inc(v_idx_1900_);
    leanh::lean_dec_ref(v_b_1898_);
    v___x_1901_ = l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__0;
    v___x_1902_ = l_Nat_reprFast(v_var_1899_);
    v___x_1903_ = lean_string_append(v___x_1901_, v___x_1902_);
    leanh::lean_dec_ref(v___x_1902_);
    v___x_1904_ = l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1;
    v___x_1905_ = lean_string_append(v___x_1903_, v___x_1904_);
    v___x_1906_ = l_Nat_reprFast(v_idx_1900_);
    v___x_1907_ = lean_string_append(v___x_1905_, v___x_1906_);
    leanh::lean_dec_ref(v___x_1906_);
    v___x_1908_ = l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2;
    v___x_1909_ = lean_string_append(v___x_1907_, v___x_1908_);
    return v___x_1909_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = leanh::lean_unsigned_to_nat(1);
    v___x_1913_ = leanh::lean_unsigned_to_nat(0);
    v___x_1914_ = lean_nat_mod(v___x_1913_, v___x_1912_);
    return v___x_1914_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1915_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0_once),
        _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__0,
    );
    v___x_1916_ = leanh::lean_unsigned_to_nat(1);
    v___x_1917_ = leanh::lean_unsigned_to_nat(0);
    v___x_1918_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1918_, 0, v___x_1917_);
    leanh::lean_ctor_set(v___x_1918_, 1, v___x_1916_);
    leanh::lean_ctor_set(v___x_1918_, 2, v___x_1915_);
    return v___x_1918_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_instInhabitedBVBit() -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1),
        core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1_once),
        _init_l_Std_Tactic_BVDecide_instInhabitedBVBit___closed__1,
    );
    return v___x_1919_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(
    mut v_x_1920_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1920_ {
        0 => {
            let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1921_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1921_;
        }
        1 => {
            let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1922_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1922_;
        }
        2 => {
            let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1923_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1923_;
        }
        3 => {
            let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1924_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1924_;
        }
        4 => {
            let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1925_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1925_;
        }
        5 => {
            let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1926_ = leanh::lean_unsigned_to_nat(5);
            return v___x_1926_;
        }
        _ => {
            let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1927_ = leanh::lean_unsigned_to_nat(6);
            return v___x_1927_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ctorIdx___boxed(
    mut v_x_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1929_: u8 = 0;
    let mut v_res_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1929_ = (leanh::lean_unbox(v_x_1928_) as u8);
    v_res_1930_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_boxed_1929_);
    return v_res_1930_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(
    mut v_x_1931_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1932_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(
    mut v_x_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1934_: u8 = 0;
    let mut v_res_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1934_ = (leanh::lean_unbox(v_x_1933_) as u8);
    v_res_1935_ = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(v_x_4__boxed_1934_);
    return v_res_1935_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(
    mut v_k_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1936_);
    return v_k_1936_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg___boxed(
    mut v_k_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1938_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim___redArg(v_k_1937_);
    leanh::lean_dec(v_k_1937_);
    return v_res_1938_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ctorElim(
    mut v_motive_1939_: *mut leanh::LeanObject,
    mut v_ctorIdx_1940_: *mut leanh::LeanObject,
    mut v_t_1941_: u8,
    mut v_h_1942_: *mut leanh::LeanObject,
    mut v_k_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1943_);
    return v_k_1943_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ctorElim___boxed(
    mut v_motive_1944_: *mut leanh::LeanObject,
    mut v_ctorIdx_1945_: *mut leanh::LeanObject,
    mut v_t_1946_: *mut leanh::LeanObject,
    mut v_h_1947_: *mut leanh::LeanObject,
    mut v_k_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1949_: u8 = 0;
    let mut v_res_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1949_ = (leanh::lean_unbox(v_t_1946_) as u8);
    v_res_1950_ = l_Std_Tactic_BVDecide_BVBinOp_ctorElim(
        v_motive_1944_,
        v_ctorIdx_1945_,
        v_t_boxed_1949_,
        v_h_1947_,
        v_k_1948_,
    );
    leanh::lean_dec(v_k_1948_);
    leanh::lean_dec(v_ctorIdx_1945_);
    return v_res_1950_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(
    mut v_and_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_and_1951_);
    return v_and_1951_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg___boxed(
    mut v_and_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1953_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim___redArg(v_and_1952_);
    leanh::lean_dec(v_and_1952_);
    return v_res_1953_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_and_elim(
    mut v_motive_1954_: *mut leanh::LeanObject,
    mut v_t_1955_: u8,
    mut v_h_1956_: *mut leanh::LeanObject,
    mut v_and_1957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_and_1957_);
    return v_and_1957_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_and_elim___boxed(
    mut v_motive_1958_: *mut leanh::LeanObject,
    mut v_t_1959_: *mut leanh::LeanObject,
    mut v_h_1960_: *mut leanh::LeanObject,
    mut v_and_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1962_: u8 = 0;
    let mut v_res_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1962_ = (leanh::lean_unbox(v_t_1959_) as u8);
    v_res_1963_ = l_Std_Tactic_BVDecide_BVBinOp_and_elim(
        v_motive_1958_,
        v_t_boxed_1962_,
        v_h_1960_,
        v_and_1961_,
    );
    leanh::lean_dec(v_and_1961_);
    return v_res_1963_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(
    mut v_or_1964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_or_1964_);
    return v_or_1964_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg___boxed(
    mut v_or_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim___redArg(v_or_1965_);
    leanh::lean_dec(v_or_1965_);
    return v_res_1966_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_or_elim(
    mut v_motive_1967_: *mut leanh::LeanObject,
    mut v_t_1968_: u8,
    mut v_h_1969_: *mut leanh::LeanObject,
    mut v_or_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_or_1970_);
    return v_or_1970_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_or_elim___boxed(
    mut v_motive_1971_: *mut leanh::LeanObject,
    mut v_t_1972_: *mut leanh::LeanObject,
    mut v_h_1973_: *mut leanh::LeanObject,
    mut v_or_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1975_: u8 = 0;
    let mut v_res_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1975_ = (leanh::lean_unbox(v_t_1972_) as u8);
    v_res_1976_ = l_Std_Tactic_BVDecide_BVBinOp_or_elim(
        v_motive_1971_,
        v_t_boxed_1975_,
        v_h_1973_,
        v_or_1974_,
    );
    leanh::lean_dec(v_or_1974_);
    return v_res_1976_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(
    mut v_xor_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_xor_1977_);
    return v_xor_1977_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg___boxed(
    mut v_xor_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1979_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim___redArg(v_xor_1978_);
    leanh::lean_dec(v_xor_1978_);
    return v_res_1979_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_xor_elim(
    mut v_motive_1980_: *mut leanh::LeanObject,
    mut v_t_1981_: u8,
    mut v_h_1982_: *mut leanh::LeanObject,
    mut v_xor_1983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_xor_1983_);
    return v_xor_1983_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_xor_elim___boxed(
    mut v_motive_1984_: *mut leanh::LeanObject,
    mut v_t_1985_: *mut leanh::LeanObject,
    mut v_h_1986_: *mut leanh::LeanObject,
    mut v_xor_1987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1988_: u8 = 0;
    let mut v_res_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1988_ = (leanh::lean_unbox(v_t_1985_) as u8);
    v_res_1989_ = l_Std_Tactic_BVDecide_BVBinOp_xor_elim(
        v_motive_1984_,
        v_t_boxed_1988_,
        v_h_1986_,
        v_xor_1987_,
    );
    leanh::lean_dec(v_xor_1987_);
    return v_res_1989_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(
    mut v_add_1990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_add_1990_);
    return v_add_1990_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg___boxed(
    mut v_add_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim___redArg(v_add_1991_);
    leanh::lean_dec(v_add_1991_);
    return v_res_1992_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_add_elim(
    mut v_motive_1993_: *mut leanh::LeanObject,
    mut v_t_1994_: u8,
    mut v_h_1995_: *mut leanh::LeanObject,
    mut v_add_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_add_1996_);
    return v_add_1996_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_add_elim___boxed(
    mut v_motive_1997_: *mut leanh::LeanObject,
    mut v_t_1998_: *mut leanh::LeanObject,
    mut v_h_1999_: *mut leanh::LeanObject,
    mut v_add_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2001_: u8 = 0;
    let mut v_res_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2001_ = (leanh::lean_unbox(v_t_1998_) as u8);
    v_res_2002_ = l_Std_Tactic_BVDecide_BVBinOp_add_elim(
        v_motive_1997_,
        v_t_boxed_2001_,
        v_h_1999_,
        v_add_2000_,
    );
    leanh::lean_dec(v_add_2000_);
    return v_res_2002_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(
    mut v_mul_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_mul_2003_);
    return v_mul_2003_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg___boxed(
    mut v_mul_2004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2005_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim___redArg(v_mul_2004_);
    leanh::lean_dec(v_mul_2004_);
    return v_res_2005_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_mul_elim(
    mut v_motive_2006_: *mut leanh::LeanObject,
    mut v_t_2007_: u8,
    mut v_h_2008_: *mut leanh::LeanObject,
    mut v_mul_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_mul_2009_);
    return v_mul_2009_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_mul_elim___boxed(
    mut v_motive_2010_: *mut leanh::LeanObject,
    mut v_t_2011_: *mut leanh::LeanObject,
    mut v_h_2012_: *mut leanh::LeanObject,
    mut v_mul_2013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2014_: u8 = 0;
    let mut v_res_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2014_ = (leanh::lean_unbox(v_t_2011_) as u8);
    v_res_2015_ = l_Std_Tactic_BVDecide_BVBinOp_mul_elim(
        v_motive_2010_,
        v_t_boxed_2014_,
        v_h_2012_,
        v_mul_2013_,
    );
    leanh::lean_dec(v_mul_2013_);
    return v_res_2015_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(
    mut v_udiv_2016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_udiv_2016_);
    return v_udiv_2016_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg___boxed(
    mut v_udiv_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___redArg(v_udiv_2017_);
    leanh::lean_dec(v_udiv_2017_);
    return v_res_2018_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(
    mut v_motive_2019_: *mut leanh::LeanObject,
    mut v_t_2020_: u8,
    mut v_h_2021_: *mut leanh::LeanObject,
    mut v_udiv_2022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_udiv_2022_);
    return v_udiv_2022_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_udiv_elim___boxed(
    mut v_motive_2023_: *mut leanh::LeanObject,
    mut v_t_2024_: *mut leanh::LeanObject,
    mut v_h_2025_: *mut leanh::LeanObject,
    mut v_udiv_2026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2027_: u8 = 0;
    let mut v_res_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2027_ = (leanh::lean_unbox(v_t_2024_) as u8);
    v_res_2028_ = l_Std_Tactic_BVDecide_BVBinOp_udiv_elim(
        v_motive_2023_,
        v_t_boxed_2027_,
        v_h_2025_,
        v_udiv_2026_,
    );
    leanh::lean_dec(v_udiv_2026_);
    return v_res_2028_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(
    mut v_umod_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_umod_2029_);
    return v_umod_2029_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg___boxed(
    mut v_umod_2030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2031_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim___redArg(v_umod_2030_);
    leanh::lean_dec(v_umod_2030_);
    return v_res_2031_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_umod_elim(
    mut v_motive_2032_: *mut leanh::LeanObject,
    mut v_t_2033_: u8,
    mut v_h_2034_: *mut leanh::LeanObject,
    mut v_umod_2035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_umod_2035_);
    return v_umod_2035_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_umod_elim___boxed(
    mut v_motive_2036_: *mut leanh::LeanObject,
    mut v_t_2037_: *mut leanh::LeanObject,
    mut v_h_2038_: *mut leanh::LeanObject,
    mut v_umod_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2040_: u8 = 0;
    let mut v_res_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2040_ = (leanh::lean_unbox(v_t_2037_) as u8);
    v_res_2041_ = l_Std_Tactic_BVDecide_BVBinOp_umod_elim(
        v_motive_2036_,
        v_t_boxed_2040_,
        v_h_2038_,
        v_umod_2039_,
    );
    leanh::lean_dec(v_umod_2039_);
    return v_res_2041_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(mut v_x_2042_: u8) -> u64 {
    match v_x_2042_ {
        0 => {
            let mut v___x_2043_: u64 = 0;
            v___x_2043_ = 0u64;
            return v___x_2043_;
        }
        1 => {
            let mut v___x_2044_: u64 = 0;
            v___x_2044_ = 1u64;
            return v___x_2044_;
        }
        2 => {
            let mut v___x_2045_: u64 = 0;
            v___x_2045_ = 2u64;
            return v___x_2045_;
        }
        3 => {
            let mut v___x_2046_: u64 = 0;
            v___x_2046_ = 3u64;
            return v___x_2046_;
        }
        4 => {
            let mut v___x_2047_: u64 = 0;
            v___x_2047_ = 4u64;
            return v___x_2047_;
        }
        5 => {
            let mut v___x_2048_: u64 = 0;
            v___x_2048_ = 5u64;
            return v___x_2048_;
        }
        _ => {
            let mut v___x_2049_: u64 = 0;
            v___x_2049_ = 6u64;
            return v___x_2049_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_instHashableBVBinOp_hash___boxed(
    mut v_x_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_88__boxed_2051_: u8 = 0;
    let mut v_res_2052_: u64 = 0;
    let mut v_r_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_88__boxed_2051_ = (leanh::lean_unbox(v_x_2050_) as u8);
    v_res_2052_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_x_88__boxed_2051_);
    v_r_2053_ = leanh::lean_box_uint64(v_res_2052_);
    return v_r_2053_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ofNat(
    mut v_n_2056_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    v___x_2057_ = leanh::lean_unsigned_to_nat(2);
    v___x_2058_ = lean_nat_dec_le(v_n_2056_, v___x_2057_);
    if v___x_2058_ == 0 {
        let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2060_: u8 = 0;
        v___x_2059_ = leanh::lean_unsigned_to_nat(4);
        v___x_2060_ = lean_nat_dec_le(v_n_2056_, v___x_2059_);
        if v___x_2060_ == 0 {
            let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2062_: u8 = 0;
            v___x_2061_ = leanh::lean_unsigned_to_nat(5);
            v___x_2062_ = lean_nat_dec_le(v_n_2056_, v___x_2061_);
            if v___x_2062_ == 0 {
                let mut v___x_2063_: u8 = 0;
                v___x_2063_ = 6;
                return v___x_2063_;
            } else {
                let mut v___x_2064_: u8 = 0;
                v___x_2064_ = 5;
                return v___x_2064_;
            }
        } else {
            let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2066_: u8 = 0;
            v___x_2065_ = leanh::lean_unsigned_to_nat(3);
            v___x_2066_ = lean_nat_dec_le(v_n_2056_, v___x_2065_);
            if v___x_2066_ == 0 {
                let mut v___x_2067_: u8 = 0;
                v___x_2067_ = 4;
                return v___x_2067_;
            } else {
                let mut v___x_2068_: u8 = 0;
                v___x_2068_ = 3;
                return v___x_2068_;
            }
        }
    } else {
        let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: u8 = 0;
        v___x_2069_ = leanh::lean_unsigned_to_nat(0);
        v___x_2070_ = lean_nat_dec_le(v_n_2056_, v___x_2069_);
        if v___x_2070_ == 0 {
            let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2072_: u8 = 0;
            v___x_2071_ = leanh::lean_unsigned_to_nat(1);
            v___x_2072_ = lean_nat_dec_le(v_n_2056_, v___x_2071_);
            if v___x_2072_ == 0 {
                let mut v___x_2073_: u8 = 0;
                v___x_2073_ = 2;
                return v___x_2073_;
            } else {
                let mut v___x_2074_: u8 = 0;
                v___x_2074_ = 1;
                return v___x_2074_;
            }
        } else {
            let mut v___x_2075_: u8 = 0;
            v___x_2075_ = 0;
            return v___x_2075_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(
    mut v_n_2076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2077_: u8 = 0;
    let mut v_r_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2077_ = l_Std_Tactic_BVDecide_BVBinOp_ofNat(v_n_2076_);
    leanh::lean_dec(v_n_2076_);
    v_r_2078_ = leanh::lean_box((v_res_2077_) as usize);
    return v_r_2078_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(
    mut v_x_2079_: u8,
    mut v_y_2080_: u8,
) -> u8 {
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    v___x_2081_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_x_2079_);
    v___x_2082_ = l_Std_Tactic_BVDecide_BVBinOp_ctorIdx(v_y_2080_);
    v___x_2083_ = lean_nat_dec_eq(v___x_2081_, v___x_2082_);
    leanh::lean_dec(v___x_2082_);
    leanh::lean_dec(v___x_2081_);
    return v___x_2083_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(
    mut v_x_2084_: *mut leanh::LeanObject,
    mut v_y_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13__boxed_2086_: u8 = 0;
    let mut v_y_14__boxed_2087_: u8 = 0;
    let mut v_res_2088_: u8 = 0;
    let mut v_r_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_2086_ = (leanh::lean_unbox(v_x_2084_) as u8);
    v_y_14__boxed_2087_ = (leanh::lean_unbox(v_y_2085_) as u8);
    v_res_2088_ =
        l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(v_x_13__boxed_2086_, v_y_14__boxed_2087_);
    v_r_2089_ = leanh::lean_box((v_res_2088_) as usize);
    return v_r_2089_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_toString(
    mut v_x_2097_: u8,
) -> *mut leanh::LeanObject {
    match v_x_2097_ {
        0 => {
            let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2098_ = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__0;
            return v___x_2098_;
        }
        1 => {
            let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2099_ = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__1;
            return v___x_2099_;
        }
        2 => {
            let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2100_ = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__2;
            return v___x_2100_;
        }
        3 => {
            let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2101_ = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__3;
            return v___x_2101_;
        }
        4 => {
            let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2102_ = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__4;
            return v___x_2102_;
        }
        5 => {
            let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2103_ = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__5;
            return v___x_2103_;
        }
        _ => {
            let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2104_ = l_Std_Tactic_BVDecide_BVBinOp_toString___closed__6;
            return v___x_2104_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(
    mut v_x_2105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_67__boxed_2106_: u8 = 0;
    let mut v_res_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_67__boxed_2106_ = (leanh::lean_unbox(v_x_2105_) as u8);
    v_res_2107_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_x_67__boxed_2106_);
    return v_res_2107_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_eval(
    mut v_w_2110_: *mut leanh::LeanObject,
    mut v_x_2111_: u8,
    mut v_a_2112_: *mut leanh::LeanObject,
    mut v_a_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match v_x_2111_ {
        0 => {
            let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2114_ = lean_nat_land(v_a_2112_, v_a_2113_);
            return v___x_2114_;
        }
        1 => {
            let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2115_ = lean_nat_lor(v_a_2112_, v_a_2113_);
            return v___x_2115_;
        }
        2 => {
            let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2116_ = lean_nat_lxor(v_a_2112_, v_a_2113_);
            return v___x_2116_;
        }
        3 => {
            let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2117_ = l_BitVec_add(v_w_2110_, v_a_2112_, v_a_2113_);
            return v___x_2117_;
        }
        4 => {
            let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2118_ = l_BitVec_mul(v_w_2110_, v_a_2112_, v_a_2113_);
            return v___x_2118_;
        }
        5 => {
            let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2119_ = lean_nat_div(v_a_2112_, v_a_2113_);
            return v___x_2119_;
        }
        _ => {
            let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2120_ = lean_nat_mod(v_a_2112_, v_a_2113_);
            return v___x_2120_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(
    mut v_w_2121_: *mut leanh::LeanObject,
    mut v_x_2122_: *mut leanh::LeanObject,
    mut v_a_2123_: *mut leanh::LeanObject,
    mut v_a_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_354__boxed_2125_: u8 = 0;
    let mut v_res_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_354__boxed_2125_ = (leanh::lean_unbox(v_x_2122_) as u8);
    v_res_2126_ =
        l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_2121_, v_x_354__boxed_2125_, v_a_2123_, v_a_2124_);
    leanh::lean_dec(v_a_2124_);
    leanh::lean_dec(v_a_2123_);
    leanh::lean_dec(v_w_2121_);
    return v_res_2126_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(
    mut v_x_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2127_) {
        0 => {
            let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2128_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2128_;
        }
        1 => {
            let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2129_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2129_;
        }
        2 => {
            let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2130_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2130_;
        }
        3 => {
            let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2131_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2131_;
        }
        4 => {
            let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2132_ = leanh::lean_unsigned_to_nat(4);
            return v___x_2132_;
        }
        5 => {
            let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2133_ = leanh::lean_unsigned_to_nat(5);
            return v___x_2133_;
        }
        _ => {
            let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2134_ = leanh::lean_unsigned_to_nat(6);
            return v___x_2134_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_ctorIdx___boxed(
    mut v_x_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2136_ = l_Std_Tactic_BVDecide_BVUnOp_ctorIdx(v_x_2135_);
    leanh::lean_dec(v_x_2135_);
    return v_res_2136_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(
    mut v_t_2137_: *mut leanh::LeanObject,
    mut v_k_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2137_) {
        1 => {
            let mut v_n_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2139_ = leanh::lean_ctor_get(v_t_2137_, 0);
            leanh::lean_inc(v_n_2139_);
            leanh::lean_dec_ref_known(v_t_2137_, 1);
            v___x_2140_ = leanh::lean_apply_1(v_k_2138_, v_n_2139_);
            return v___x_2140_;
        }
        2 => {
            let mut v_n_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2141_ = leanh::lean_ctor_get(v_t_2137_, 0);
            leanh::lean_inc(v_n_2141_);
            leanh::lean_dec_ref_known(v_t_2137_, 1);
            v___x_2142_ = leanh::lean_apply_1(v_k_2138_, v_n_2141_);
            return v___x_2142_;
        }
        3 => {
            let mut v_n_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2143_ = leanh::lean_ctor_get(v_t_2137_, 0);
            leanh::lean_inc(v_n_2143_);
            leanh::lean_dec_ref_known(v_t_2137_, 1);
            v___x_2144_ = leanh::lean_apply_1(v_k_2138_, v_n_2143_);
            return v___x_2144_;
        }
        _ => {
            leanh::lean_dec(v_t_2137_);
            return v_k_2138_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_ctorElim(
    mut v_motive_2145_: *mut leanh::LeanObject,
    mut v_ctorIdx_2146_: *mut leanh::LeanObject,
    mut v_t_2147_: *mut leanh::LeanObject,
    mut v_h_2148_: *mut leanh::LeanObject,
    mut v_k_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2147_, v_k_2149_);
    return v___x_2150_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_ctorElim___boxed(
    mut v_motive_2151_: *mut leanh::LeanObject,
    mut v_ctorIdx_2152_: *mut leanh::LeanObject,
    mut v_t_2153_: *mut leanh::LeanObject,
    mut v_h_2154_: *mut leanh::LeanObject,
    mut v_k_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim(
        v_motive_2151_,
        v_ctorIdx_2152_,
        v_t_2153_,
        v_h_2154_,
        v_k_2155_,
    );
    leanh::lean_dec(v_ctorIdx_2152_);
    return v_res_2156_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_not_elim___redArg(
    mut v_t_2157_: *mut leanh::LeanObject,
    mut v_not_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2157_, v_not_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_not_elim(
    mut v_motive_2160_: *mut leanh::LeanObject,
    mut v_t_2161_: *mut leanh::LeanObject,
    mut v_h_2162_: *mut leanh::LeanObject,
    mut v_not_2163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2164_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2161_, v_not_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim___redArg(
    mut v_t_2165_: *mut leanh::LeanObject,
    mut v_rotateLeft_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2167_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2165_, v_rotateLeft_2166_);
    return v___x_2167_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_rotateLeft_elim(
    mut v_motive_2168_: *mut leanh::LeanObject,
    mut v_t_2169_: *mut leanh::LeanObject,
    mut v_h_2170_: *mut leanh::LeanObject,
    mut v_rotateLeft_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2169_, v_rotateLeft_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim___redArg(
    mut v_t_2173_: *mut leanh::LeanObject,
    mut v_rotateRight_2174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2175_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2173_, v_rotateRight_2174_);
    return v___x_2175_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_rotateRight_elim(
    mut v_motive_2176_: *mut leanh::LeanObject,
    mut v_t_2177_: *mut leanh::LeanObject,
    mut v_h_2178_: *mut leanh::LeanObject,
    mut v_rotateRight_2179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2177_, v_rotateRight_2179_);
    return v___x_2180_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim___redArg(
    mut v_t_2181_: *mut leanh::LeanObject,
    mut v_arithShiftRightConst_2182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ =
        l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2181_, v_arithShiftRightConst_2182_);
    return v___x_2183_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_arithShiftRightConst_elim(
    mut v_motive_2184_: *mut leanh::LeanObject,
    mut v_t_2185_: *mut leanh::LeanObject,
    mut v_h_2186_: *mut leanh::LeanObject,
    mut v_arithShiftRightConst_2187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ =
        l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2185_, v_arithShiftRightConst_2187_);
    return v___x_2188_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_reverse_elim___redArg(
    mut v_t_2189_: *mut leanh::LeanObject,
    mut v_reverse_2190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2189_, v_reverse_2190_);
    return v___x_2191_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_reverse_elim(
    mut v_motive_2192_: *mut leanh::LeanObject,
    mut v_t_2193_: *mut leanh::LeanObject,
    mut v_h_2194_: *mut leanh::LeanObject,
    mut v_reverse_2195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2193_, v_reverse_2195_);
    return v___x_2196_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_clz_elim___redArg(
    mut v_t_2197_: *mut leanh::LeanObject,
    mut v_clz_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2197_, v_clz_2198_);
    return v___x_2199_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_clz_elim(
    mut v_motive_2200_: *mut leanh::LeanObject,
    mut v_t_2201_: *mut leanh::LeanObject,
    mut v_h_2202_: *mut leanh::LeanObject,
    mut v_clz_2203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2204_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2201_, v_clz_2203_);
    return v___x_2204_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_cpop_elim___redArg(
    mut v_t_2205_: *mut leanh::LeanObject,
    mut v_cpop_2206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2205_, v_cpop_2206_);
    return v___x_2207_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_cpop_elim(
    mut v_motive_2208_: *mut leanh::LeanObject,
    mut v_t_2209_: *mut leanh::LeanObject,
    mut v_h_2210_: *mut leanh::LeanObject,
    mut v_cpop_2211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2212_ = l_Std_Tactic_BVDecide_BVUnOp_ctorElim___redArg(v_t_2209_, v_cpop_2211_);
    return v___x_2212_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(
    mut v_x_2213_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_x_2213_) {
        0 => {
            let mut v___x_2214_: u64 = 0;
            v___x_2214_ = 0u64;
            return v___x_2214_;
        }
        1 => {
            let mut v_n_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2216_: u64 = 0;
            let mut v___x_2217_: u64 = 0;
            let mut v___x_2218_: u64 = 0;
            v_n_2215_ = leanh::lean_ctor_get(v_x_2213_, 0);
            v___x_2216_ = 1u64;
            v___x_2217_ = lean_uint64_of_nat(v_n_2215_);
            v___x_2218_ = lean_uint64_mix_hash(v___x_2216_, v___x_2217_);
            return v___x_2218_;
        }
        2 => {
            let mut v_n_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2220_: u64 = 0;
            let mut v___x_2221_: u64 = 0;
            let mut v___x_2222_: u64 = 0;
            v_n_2219_ = leanh::lean_ctor_get(v_x_2213_, 0);
            v___x_2220_ = 2u64;
            v___x_2221_ = lean_uint64_of_nat(v_n_2219_);
            v___x_2222_ = lean_uint64_mix_hash(v___x_2220_, v___x_2221_);
            return v___x_2222_;
        }
        3 => {
            let mut v_n_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2224_: u64 = 0;
            let mut v___x_2225_: u64 = 0;
            let mut v___x_2226_: u64 = 0;
            v_n_2223_ = leanh::lean_ctor_get(v_x_2213_, 0);
            v___x_2224_ = 3u64;
            v___x_2225_ = lean_uint64_of_nat(v_n_2223_);
            v___x_2226_ = lean_uint64_mix_hash(v___x_2224_, v___x_2225_);
            return v___x_2226_;
        }
        4 => {
            let mut v___x_2227_: u64 = 0;
            v___x_2227_ = 4u64;
            return v___x_2227_;
        }
        5 => {
            let mut v___x_2228_: u64 = 0;
            v___x_2228_ = 5u64;
            return v___x_2228_;
        }
        _ => {
            let mut v___x_2229_: u64 = 0;
            v___x_2229_ = 6u64;
            return v___x_2229_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_instHashableBVUnOp_hash___boxed(
    mut v_x_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2231_: u64 = 0;
    let mut v_r_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_x_2230_);
    leanh::lean_dec(v_x_2230_);
    v_r_2232_ = leanh::lean_box_uint64(v_res_2231_);
    return v_r_2232_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(
    mut v_x_2235_: *mut leanh::LeanObject,
    mut v_x_2236_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_2235_) {
        0 => match leanh::lean_obj_tag(v_x_2236_) {
            0 => {
                let mut v___x_2237_: u8 = 0;
                v___x_2237_ = 1;
                return v___x_2237_;
            }
            4 => {
                let mut v___x_2238_: u8 = 0;
                v___x_2238_ = 0;
                return v___x_2238_;
            }
            5 => {
                let mut v___x_2239_: u8 = 0;
                v___x_2239_ = 0;
                return v___x_2239_;
            }
            6 => {
                let mut v___x_2240_: u8 = 0;
                v___x_2240_ = 0;
                return v___x_2240_;
            }
            _ => {
                let mut v___x_2241_: u8 = 0;
                v___x_2241_ = 0;
                return v___x_2241_;
            }
        },
        1 => {
            let mut v_n_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2243_: u8 = 0;
            v_n_2242_ = leanh::lean_ctor_get(v_x_2235_, 0);
            v___x_2243_ = 0;
            match leanh::lean_obj_tag(v_x_2236_) {
                0 => {
                    return v___x_2243_;
                }
                1 => {
                    let mut v_n_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2245_: u8 = 0;
                    v_n_2244_ = leanh::lean_ctor_get(v_x_2236_, 0);
                    v___x_2245_ = lean_nat_dec_eq(v_n_2242_, v_n_2244_);
                    if v___x_2245_ == 0 {
                        return v___x_2243_;
                    } else {
                        return v___x_2245_;
                    }
                }
                4 => {
                    return v___x_2243_;
                }
                5 => {
                    return v___x_2243_;
                }
                6 => {
                    return v___x_2243_;
                }
                _ => {
                    return v___x_2243_;
                }
            }
        }
        2 => {
            let mut v_n_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2247_: u8 = 0;
            v_n_2246_ = leanh::lean_ctor_get(v_x_2235_, 0);
            v___x_2247_ = 0;
            match leanh::lean_obj_tag(v_x_2236_) {
                0 => {
                    return v___x_2247_;
                }
                2 => {
                    let mut v_n_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2249_: u8 = 0;
                    v_n_2248_ = leanh::lean_ctor_get(v_x_2236_, 0);
                    v___x_2249_ = lean_nat_dec_eq(v_n_2246_, v_n_2248_);
                    if v___x_2249_ == 0 {
                        return v___x_2247_;
                    } else {
                        return v___x_2249_;
                    }
                }
                4 => {
                    return v___x_2247_;
                }
                5 => {
                    return v___x_2247_;
                }
                6 => {
                    return v___x_2247_;
                }
                _ => {
                    return v___x_2247_;
                }
            }
        }
        3 => {
            let mut v_n_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2251_: u8 = 0;
            v_n_2250_ = leanh::lean_ctor_get(v_x_2235_, 0);
            v___x_2251_ = 0;
            match leanh::lean_obj_tag(v_x_2236_) {
                0 => {
                    return v___x_2251_;
                }
                3 => {
                    let mut v_n_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2253_: u8 = 0;
                    v_n_2252_ = leanh::lean_ctor_get(v_x_2236_, 0);
                    v___x_2253_ = lean_nat_dec_eq(v_n_2250_, v_n_2252_);
                    if v___x_2253_ == 0 {
                        return v___x_2251_;
                    } else {
                        return v___x_2253_;
                    }
                }
                4 => {
                    return v___x_2251_;
                }
                5 => {
                    return v___x_2251_;
                }
                6 => {
                    return v___x_2251_;
                }
                _ => {
                    return v___x_2251_;
                }
            }
        }
        4 => match leanh::lean_obj_tag(v_x_2236_) {
            1 => {
                let mut v___x_2254_: u8 = 0;
                v___x_2254_ = 0;
                return v___x_2254_;
            }
            2 => {
                let mut v___x_2255_: u8 = 0;
                v___x_2255_ = 0;
                return v___x_2255_;
            }
            3 => {
                let mut v___x_2256_: u8 = 0;
                v___x_2256_ = 0;
                return v___x_2256_;
            }
            4 => {
                let mut v___x_2257_: u8 = 0;
                v___x_2257_ = 1;
                return v___x_2257_;
            }
            _ => {
                let mut v___x_2258_: u8 = 0;
                v___x_2258_ = 0;
                return v___x_2258_;
            }
        },
        5 => match leanh::lean_obj_tag(v_x_2236_) {
            1 => {
                let mut v___x_2259_: u8 = 0;
                v___x_2259_ = 0;
                return v___x_2259_;
            }
            2 => {
                let mut v___x_2260_: u8 = 0;
                v___x_2260_ = 0;
                return v___x_2260_;
            }
            3 => {
                let mut v___x_2261_: u8 = 0;
                v___x_2261_ = 0;
                return v___x_2261_;
            }
            5 => {
                let mut v___x_2262_: u8 = 0;
                v___x_2262_ = 1;
                return v___x_2262_;
            }
            _ => {
                let mut v___x_2263_: u8 = 0;
                v___x_2263_ = 0;
                return v___x_2263_;
            }
        },
        _ => match leanh::lean_obj_tag(v_x_2236_) {
            1 => {
                let mut v___x_2264_: u8 = 0;
                v___x_2264_ = 0;
                return v___x_2264_;
            }
            2 => {
                let mut v___x_2265_: u8 = 0;
                v___x_2265_ = 0;
                return v___x_2265_;
            }
            3 => {
                let mut v___x_2266_: u8 = 0;
                v___x_2266_ = 0;
                return v___x_2266_;
            }
            6 => {
                let mut v___x_2267_: u8 = 0;
                v___x_2267_ = 1;
                return v___x_2267_;
            }
            _ => {
                let mut v___x_2268_: u8 = 0;
                v___x_2268_ = 0;
                return v___x_2268_;
            }
        },
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq___boxed(
    mut v_x_2269_: *mut leanh::LeanObject,
    mut v_x_2270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2271_: u8 = 0;
    let mut v_r_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2271_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_2269_, v_x_2270_);
    leanh::lean_dec(v_x_2270_);
    leanh::lean_dec(v_x_2269_);
    v_r_2272_ = leanh::lean_box((v_res_2271_) as usize);
    return v_r_2272_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(
    mut v_x_2273_: *mut leanh::LeanObject,
    mut v_x_2274_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2275_: u8 = 0;
    v___x_2275_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(v_x_2273_, v_x_2274_);
    return v___x_2275_;
}
pub unsafe fn l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(
    mut v_x_2276_: *mut leanh::LeanObject,
    mut v_x_2277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2278_: u8 = 0;
    let mut v_r_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(v_x_2276_, v_x_2277_);
    leanh::lean_dec(v_x_2277_);
    leanh::lean_dec(v_x_2276_);
    v_r_2279_ = leanh::lean_box((v_res_2278_) as usize);
    return v_r_2279_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_toString(
    mut v_x_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2287_) {
        0 => {
            let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2288_ = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__0;
            return v___x_2288_;
        }
        1 => {
            let mut v_n_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2289_ = leanh::lean_ctor_get(v_x_2287_, 0);
            leanh::lean_inc(v_n_2289_);
            leanh::lean_dec_ref_known(v_x_2287_, 1);
            v___x_2290_ = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__1;
            v___x_2291_ = l_Nat_reprFast(v_n_2289_);
            v___x_2292_ = lean_string_append(v___x_2290_, v___x_2291_);
            leanh::lean_dec_ref(v___x_2291_);
            return v___x_2292_;
        }
        2 => {
            let mut v_n_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2293_ = leanh::lean_ctor_get(v_x_2287_, 0);
            leanh::lean_inc(v_n_2293_);
            leanh::lean_dec_ref_known(v_x_2287_, 1);
            v___x_2294_ = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__2;
            v___x_2295_ = l_Nat_reprFast(v_n_2293_);
            v___x_2296_ = lean_string_append(v___x_2294_, v___x_2295_);
            leanh::lean_dec_ref(v___x_2295_);
            return v___x_2296_;
        }
        3 => {
            let mut v_n_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2297_ = leanh::lean_ctor_get(v_x_2287_, 0);
            leanh::lean_inc(v_n_2297_);
            leanh::lean_dec_ref_known(v_x_2287_, 1);
            v___x_2298_ = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__3;
            v___x_2299_ = l_Nat_reprFast(v_n_2297_);
            v___x_2300_ = lean_string_append(v___x_2298_, v___x_2299_);
            leanh::lean_dec_ref(v___x_2299_);
            return v___x_2300_;
        }
        4 => {
            let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2301_ = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__4;
            return v___x_2301_;
        }
        5 => {
            let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2302_ = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__5;
            return v___x_2302_;
        }
        _ => {
            let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2303_ = l_Std_Tactic_BVDecide_BVUnOp_toString___closed__6;
            return v___x_2303_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_eval(
    mut v_w_2306_: *mut leanh::LeanObject,
    mut v_x_2307_: *mut leanh::LeanObject,
    mut v_a_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2307_) {
        0 => {
            let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2309_ = l_BitVec_not(v_w_2306_, v_a_2308_);
            leanh::lean_dec(v_a_2308_);
            leanh::lean_dec(v_w_2306_);
            return v___x_2309_;
        }
        1 => {
            let mut v_n_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2310_ = leanh::lean_ctor_get(v_x_2307_, 0);
            v___x_2311_ = l_BitVec_rotateLeft(v_w_2306_, v_a_2308_, v_n_2310_);
            leanh::lean_dec(v_a_2308_);
            leanh::lean_dec(v_w_2306_);
            return v___x_2311_;
        }
        2 => {
            let mut v_n_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2312_ = leanh::lean_ctor_get(v_x_2307_, 0);
            v___x_2313_ = l_BitVec_rotateRight(v_w_2306_, v_a_2308_, v_n_2312_);
            leanh::lean_dec(v_a_2308_);
            leanh::lean_dec(v_w_2306_);
            return v___x_2313_;
        }
        3 => {
            let mut v_n_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_2314_ = leanh::lean_ctor_get(v_x_2307_, 0);
            v___x_2315_ = l_BitVec_sshiftRight(v_w_2306_, v_a_2308_, v_n_2314_);
            leanh::lean_dec(v_w_2306_);
            return v___x_2315_;
        }
        4 => {
            let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2316_ = l_BitVec_reverse(v_w_2306_, v_a_2308_);
            leanh::lean_dec(v_a_2308_);
            leanh::lean_dec(v_w_2306_);
            return v___x_2316_;
        }
        5 => {
            let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2317_ = l_BitVec_clz(v_w_2306_, v_a_2308_);
            leanh::lean_dec(v_a_2308_);
            leanh::lean_dec(v_w_2306_);
            return v___x_2317_;
        }
        _ => {
            let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2318_ = l_BitVec_cpop(v_w_2306_, v_a_2308_);
            leanh::lean_dec(v_a_2308_);
            return v___x_2318_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(
    mut v_w_2319_: *mut leanh::LeanObject,
    mut v_x_2320_: *mut leanh::LeanObject,
    mut v_a_2321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2322_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_2319_, v_x_2320_, v_a_2321_);
    leanh::lean_dec(v_x_2320_);
    return v_res_2322_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(
    mut v_x_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2323_) {
        0 => {
            let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2324_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2324_;
        }
        1 => {
            let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2325_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2325_;
        }
        2 => {
            let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2326_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2326_;
        }
        3 => {
            let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2327_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2327_;
        }
        4 => {
            let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2328_ = leanh::lean_unsigned_to_nat(4);
            return v___x_2328_;
        }
        5 => {
            let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2329_ = leanh::lean_unsigned_to_nat(5);
            return v___x_2329_;
        }
        6 => {
            let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2330_ = leanh::lean_unsigned_to_nat(6);
            return v___x_2330_;
        }
        7 => {
            let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2331_ = leanh::lean_unsigned_to_nat(7);
            return v___x_2331_;
        }
        8 => {
            let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2332_ = leanh::lean_unsigned_to_nat(8);
            return v___x_2332_;
        }
        _ => {
            let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2333_ = leanh::lean_unsigned_to_nat(9);
            return v___x_2333_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg___boxed(
    mut v_x_2334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2335_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_2334_);
    leanh::lean_dec_ref(v_x_2334_);
    return v_res_2335_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_ctorIdx(
    mut v_a_2336_: *mut leanh::LeanObject,
    mut v_x_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx___redArg(v_x_2337_);
    return v___x_2338_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_ctorIdx___boxed(
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_x_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Std_Tactic_BVDecide_BVExpr_ctorIdx(v_a_2339_, v_x_2340_);
    leanh::lean_dec_ref(v_x_2340_);
    leanh::lean_dec(v_a_2339_);
    return v_res_2341_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(
    mut v_t_2342_: *mut leanh::LeanObject,
    mut v_k_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2342_) {
        0 => {
            let mut v_w_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_2344_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_w_2344_);
            v_idx_2345_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc(v_idx_2345_);
            leanh::lean_dec_ref_known(v_t_2342_, 2);
            v___x_2346_ = leanh::lean_apply_2(v_k_2343_, v_w_2344_, v_idx_2345_);
            return v___x_2346_;
        }
        1 => {
            let mut v_w_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_2347_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_w_2347_);
            v_val_2348_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc(v_val_2348_);
            leanh::lean_dec_ref_known(v_t_2342_, 2);
            v___x_2349_ = leanh::lean_apply_2(v_k_2343_, v_w_2347_, v_val_2348_);
            return v___x_2349_;
        }
        2 => {
            let mut v_w_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_len_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_2350_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_w_2350_);
            v_start_2351_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc(v_start_2351_);
            v_len_2352_ = leanh::lean_ctor_get(v_t_2342_, 2);
            leanh::lean_inc(v_len_2352_);
            v_expr_2353_ = leanh::lean_ctor_get(v_t_2342_, 3);
            leanh::lean_inc_ref(v_expr_2353_);
            leanh::lean_dec_ref_known(v_t_2342_, 4);
            v___x_2354_ = leanh::lean_apply_4(
                v_k_2343_,
                v_w_2350_,
                v_start_2351_,
                v_len_2352_,
                v_expr_2353_,
            );
            return v___x_2354_;
        }
        3 => {
            let mut v_w_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_2357_: u8 = 0;
            let mut v_rhs_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_2355_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_w_2355_);
            v_lhs_2356_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc_ref(v_lhs_2356_);
            v_op_2357_ = leanh::lean_ctor_get_uint8(
                v_t_2342_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            v_rhs_2358_ = leanh::lean_ctor_get(v_t_2342_, 2);
            leanh::lean_inc_ref(v_rhs_2358_);
            leanh::lean_dec_ref_known(v_t_2342_, 3);
            v___x_2359_ = leanh::lean_box((v_op_2357_) as usize);
            v___x_2360_ = leanh::lean_apply_4(
                v_k_2343_,
                v_w_2355_,
                v_lhs_2356_,
                v___x_2359_,
                v_rhs_2358_,
            );
            return v___x_2360_;
        }
        4 => {
            let mut v_w_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_2361_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_w_2361_);
            v_op_2362_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc(v_op_2362_);
            v_operand_2363_ = leanh::lean_ctor_get(v_t_2342_, 2);
            leanh::lean_inc_ref(v_operand_2363_);
            leanh::lean_dec_ref_known(v_t_2342_, 3);
            v___x_2364_ =
                leanh::lean_apply_3(v_k_2343_, v_w_2361_, v_op_2362_, v_operand_2363_);
            return v___x_2364_;
        }
        5 => {
            let mut v_l_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_w_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_l_2365_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_l_2365_);
            v_r_2366_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc(v_r_2366_);
            v_w_2367_ = leanh::lean_ctor_get(v_t_2342_, 2);
            leanh::lean_inc(v_w_2367_);
            v_lhs_2368_ = leanh::lean_ctor_get(v_t_2342_, 3);
            leanh::lean_inc_ref(v_lhs_2368_);
            v_rhs_2369_ = leanh::lean_ctor_get(v_t_2342_, 4);
            leanh::lean_inc_ref(v_rhs_2369_);
            leanh::lean_dec_ref_known(v_t_2342_, 5);
            v___x_2370_ = leanh::lean_apply_6(
                v_k_2343_,
                v_l_2365_,
                v_r_2366_,
                v_w_2367_,
                v_lhs_2368_,
                v_rhs_2369_,
                leanh::lean_box(0),
            );
            return v___x_2370_;
        }
        6 => {
            let mut v_w_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_w_x27_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_2371_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_w_2371_);
            v_w_x27_2372_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc(v_w_x27_2372_);
            v_n_2373_ = leanh::lean_ctor_get(v_t_2342_, 2);
            leanh::lean_inc(v_n_2373_);
            v_expr_2374_ = leanh::lean_ctor_get(v_t_2342_, 3);
            leanh::lean_inc_ref(v_expr_2374_);
            leanh::lean_dec_ref_known(v_t_2342_, 4);
            v___x_2375_ = leanh::lean_apply_5(
                v_k_2343_,
                v_w_2371_,
                v_w_x27_2372_,
                v_n_2373_,
                v_expr_2374_,
                leanh::lean_box(0),
            );
            return v___x_2375_;
        }
        _ => {
            let mut v_m_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_m_2376_ = leanh::lean_ctor_get(v_t_2342_, 0);
            leanh::lean_inc(v_m_2376_);
            v_n_2377_ = leanh::lean_ctor_get(v_t_2342_, 1);
            leanh::lean_inc(v_n_2377_);
            v_lhs_2378_ = leanh::lean_ctor_get(v_t_2342_, 2);
            leanh::lean_inc_ref(v_lhs_2378_);
            v_rhs_2379_ = leanh::lean_ctor_get(v_t_2342_, 3);
            leanh::lean_inc_ref(v_rhs_2379_);
            leanh::lean_dec_ref(v_t_2342_);
            v___x_2380_ = leanh::lean_apply_4(
                v_k_2343_,
                v_m_2376_,
                v_n_2377_,
                v_lhs_2378_,
                v_rhs_2379_,
            );
            return v___x_2380_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_ctorElim(
    mut v_motive_2381_: *mut leanh::LeanObject,
    mut v_ctorIdx_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
    mut v_t_2384_: *mut leanh::LeanObject,
    mut v_h_2385_: *mut leanh::LeanObject,
    mut v_k_2386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2387_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2384_, v_k_2386_);
    return v___x_2387_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_ctorElim___boxed(
    mut v_motive_2388_: *mut leanh::LeanObject,
    mut v_ctorIdx_2389_: *mut leanh::LeanObject,
    mut v_a_2390_: *mut leanh::LeanObject,
    mut v_t_2391_: *mut leanh::LeanObject,
    mut v_h_2392_: *mut leanh::LeanObject,
    mut v_k_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2394_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim(
        v_motive_2388_,
        v_ctorIdx_2389_,
        v_a_2390_,
        v_t_2391_,
        v_h_2392_,
        v_k_2393_,
    );
    leanh::lean_dec(v_a_2390_);
    leanh::lean_dec(v_ctorIdx_2389_);
    return v_res_2394_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_var_elim___redArg(
    mut v_t_2395_: *mut leanh::LeanObject,
    mut v_var_2396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2395_, v_var_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_var_elim(
    mut v_motive_2398_: *mut leanh::LeanObject,
    mut v_a_2399_: *mut leanh::LeanObject,
    mut v_t_2400_: *mut leanh::LeanObject,
    mut v_h_2401_: *mut leanh::LeanObject,
    mut v_var_2402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2403_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2400_, v_var_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_var_elim___boxed(
    mut v_motive_2404_: *mut leanh::LeanObject,
    mut v_a_2405_: *mut leanh::LeanObject,
    mut v_t_2406_: *mut leanh::LeanObject,
    mut v_h_2407_: *mut leanh::LeanObject,
    mut v_var_2408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2409_ = l_Std_Tactic_BVDecide_BVExpr_var_elim(
        v_motive_2404_,
        v_a_2405_,
        v_t_2406_,
        v_h_2407_,
        v_var_2408_,
    );
    leanh::lean_dec(v_a_2405_);
    return v_res_2409_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_const_elim___redArg(
    mut v_t_2410_: *mut leanh::LeanObject,
    mut v_const_2411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2410_, v_const_2411_);
    return v___x_2412_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_const_elim(
    mut v_motive_2413_: *mut leanh::LeanObject,
    mut v_a_2414_: *mut leanh::LeanObject,
    mut v_t_2415_: *mut leanh::LeanObject,
    mut v_h_2416_: *mut leanh::LeanObject,
    mut v_const_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2415_, v_const_2417_);
    return v___x_2418_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_const_elim___boxed(
    mut v_motive_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
    mut v_t_2421_: *mut leanh::LeanObject,
    mut v_h_2422_: *mut leanh::LeanObject,
    mut v_const_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_Std_Tactic_BVDecide_BVExpr_const_elim(
        v_motive_2419_,
        v_a_2420_,
        v_t_2421_,
        v_h_2422_,
        v_const_2423_,
    );
    leanh::lean_dec(v_a_2420_);
    return v_res_2424_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_extract_elim___redArg(
    mut v_t_2425_: *mut leanh::LeanObject,
    mut v_extract_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2425_, v_extract_2426_);
    return v___x_2427_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_extract_elim(
    mut v_motive_2428_: *mut leanh::LeanObject,
    mut v_a_2429_: *mut leanh::LeanObject,
    mut v_t_2430_: *mut leanh::LeanObject,
    mut v_h_2431_: *mut leanh::LeanObject,
    mut v_extract_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2430_, v_extract_2432_);
    return v___x_2433_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_extract_elim___boxed(
    mut v_motive_2434_: *mut leanh::LeanObject,
    mut v_a_2435_: *mut leanh::LeanObject,
    mut v_t_2436_: *mut leanh::LeanObject,
    mut v_h_2437_: *mut leanh::LeanObject,
    mut v_extract_2438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2439_ = l_Std_Tactic_BVDecide_BVExpr_extract_elim(
        v_motive_2434_,
        v_a_2435_,
        v_t_2436_,
        v_h_2437_,
        v_extract_2438_,
    );
    leanh::lean_dec(v_a_2435_);
    return v_res_2439_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bin_elim___redArg(
    mut v_t_2440_: *mut leanh::LeanObject,
    mut v_bin_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2440_, v_bin_2441_);
    return v___x_2442_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bin_elim(
    mut v_motive_2443_: *mut leanh::LeanObject,
    mut v_a_2444_: *mut leanh::LeanObject,
    mut v_t_2445_: *mut leanh::LeanObject,
    mut v_h_2446_: *mut leanh::LeanObject,
    mut v_bin_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2445_, v_bin_2447_);
    return v___x_2448_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bin_elim___boxed(
    mut v_motive_2449_: *mut leanh::LeanObject,
    mut v_a_2450_: *mut leanh::LeanObject,
    mut v_t_2451_: *mut leanh::LeanObject,
    mut v_h_2452_: *mut leanh::LeanObject,
    mut v_bin_2453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2454_ = l_Std_Tactic_BVDecide_BVExpr_bin_elim(
        v_motive_2449_,
        v_a_2450_,
        v_t_2451_,
        v_h_2452_,
        v_bin_2453_,
    );
    leanh::lean_dec(v_a_2450_);
    return v_res_2454_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_un_elim___redArg(
    mut v_t_2455_: *mut leanh::LeanObject,
    mut v_un_2456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2455_, v_un_2456_);
    return v___x_2457_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_un_elim(
    mut v_motive_2458_: *mut leanh::LeanObject,
    mut v_a_2459_: *mut leanh::LeanObject,
    mut v_t_2460_: *mut leanh::LeanObject,
    mut v_h_2461_: *mut leanh::LeanObject,
    mut v_un_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2460_, v_un_2462_);
    return v___x_2463_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_un_elim___boxed(
    mut v_motive_2464_: *mut leanh::LeanObject,
    mut v_a_2465_: *mut leanh::LeanObject,
    mut v_t_2466_: *mut leanh::LeanObject,
    mut v_h_2467_: *mut leanh::LeanObject,
    mut v_un_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2469_ = l_Std_Tactic_BVDecide_BVExpr_un_elim(
        v_motive_2464_,
        v_a_2465_,
        v_t_2466_,
        v_h_2467_,
        v_un_2468_,
    );
    leanh::lean_dec(v_a_2465_);
    return v_res_2469_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_append_elim___redArg(
    mut v_t_2470_: *mut leanh::LeanObject,
    mut v_append_2471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2470_, v_append_2471_);
    return v___x_2472_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_append_elim(
    mut v_motive_2473_: *mut leanh::LeanObject,
    mut v_a_2474_: *mut leanh::LeanObject,
    mut v_t_2475_: *mut leanh::LeanObject,
    mut v_h_2476_: *mut leanh::LeanObject,
    mut v_append_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2478_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2475_, v_append_2477_);
    return v___x_2478_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_append_elim___boxed(
    mut v_motive_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
    mut v_t_2481_: *mut leanh::LeanObject,
    mut v_h_2482_: *mut leanh::LeanObject,
    mut v_append_2483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l_Std_Tactic_BVDecide_BVExpr_append_elim(
        v_motive_2479_,
        v_a_2480_,
        v_t_2481_,
        v_h_2482_,
        v_append_2483_,
    );
    leanh::lean_dec(v_a_2480_);
    return v_res_2484_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_replicate_elim___redArg(
    mut v_t_2485_: *mut leanh::LeanObject,
    mut v_replicate_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2485_, v_replicate_2486_);
    return v___x_2487_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_replicate_elim(
    mut v_motive_2488_: *mut leanh::LeanObject,
    mut v_a_2489_: *mut leanh::LeanObject,
    mut v_t_2490_: *mut leanh::LeanObject,
    mut v_h_2491_: *mut leanh::LeanObject,
    mut v_replicate_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2493_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2490_, v_replicate_2492_);
    return v___x_2493_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_replicate_elim___boxed(
    mut v_motive_2494_: *mut leanh::LeanObject,
    mut v_a_2495_: *mut leanh::LeanObject,
    mut v_t_2496_: *mut leanh::LeanObject,
    mut v_h_2497_: *mut leanh::LeanObject,
    mut v_replicate_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2499_ = l_Std_Tactic_BVDecide_BVExpr_replicate_elim(
        v_motive_2494_,
        v_a_2495_,
        v_t_2496_,
        v_h_2497_,
        v_replicate_2498_,
    );
    leanh::lean_dec(v_a_2495_);
    return v_res_2499_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___redArg(
    mut v_t_2500_: *mut leanh::LeanObject,
    mut v_shiftLeft_2501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2502_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2500_, v_shiftLeft_2501_);
    return v___x_2502_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(
    mut v_motive_2503_: *mut leanh::LeanObject,
    mut v_a_2504_: *mut leanh::LeanObject,
    mut v_t_2505_: *mut leanh::LeanObject,
    mut v_h_2506_: *mut leanh::LeanObject,
    mut v_shiftLeft_2507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2505_, v_shiftLeft_2507_);
    return v___x_2508_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim___boxed(
    mut v_motive_2509_: *mut leanh::LeanObject,
    mut v_a_2510_: *mut leanh::LeanObject,
    mut v_t_2511_: *mut leanh::LeanObject,
    mut v_h_2512_: *mut leanh::LeanObject,
    mut v_shiftLeft_2513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2514_ = l_Std_Tactic_BVDecide_BVExpr_shiftLeft_elim(
        v_motive_2509_,
        v_a_2510_,
        v_t_2511_,
        v_h_2512_,
        v_shiftLeft_2513_,
    );
    leanh::lean_dec(v_a_2510_);
    return v_res_2514_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___redArg(
    mut v_t_2515_: *mut leanh::LeanObject,
    mut v_shiftRight_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2517_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2515_, v_shiftRight_2516_);
    return v___x_2517_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(
    mut v_motive_2518_: *mut leanh::LeanObject,
    mut v_a_2519_: *mut leanh::LeanObject,
    mut v_t_2520_: *mut leanh::LeanObject,
    mut v_h_2521_: *mut leanh::LeanObject,
    mut v_shiftRight_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2523_ = l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2520_, v_shiftRight_2522_);
    return v___x_2523_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim___boxed(
    mut v_motive_2524_: *mut leanh::LeanObject,
    mut v_a_2525_: *mut leanh::LeanObject,
    mut v_t_2526_: *mut leanh::LeanObject,
    mut v_h_2527_: *mut leanh::LeanObject,
    mut v_shiftRight_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_Tactic_BVDecide_BVExpr_shiftRight_elim(
        v_motive_2524_,
        v_a_2525_,
        v_t_2526_,
        v_h_2527_,
        v_shiftRight_2528_,
    );
    leanh::lean_dec(v_a_2525_);
    return v_res_2529_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___redArg(
    mut v_t_2530_: *mut leanh::LeanObject,
    mut v_arithShiftRight_2531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ =
        l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2530_, v_arithShiftRight_2531_);
    return v___x_2532_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(
    mut v_motive_2533_: *mut leanh::LeanObject,
    mut v_a_2534_: *mut leanh::LeanObject,
    mut v_t_2535_: *mut leanh::LeanObject,
    mut v_h_2536_: *mut leanh::LeanObject,
    mut v_arithShiftRight_2537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2538_ =
        l_Std_Tactic_BVDecide_BVExpr_ctorElim___redArg(v_t_2535_, v_arithShiftRight_2537_);
    return v___x_2538_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim___boxed(
    mut v_motive_2539_: *mut leanh::LeanObject,
    mut v_a_2540_: *mut leanh::LeanObject,
    mut v_t_2541_: *mut leanh::LeanObject,
    mut v_h_2542_: *mut leanh::LeanObject,
    mut v_arithShiftRight_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_Std_Tactic_BVDecide_BVExpr_arithShiftRight_elim(
        v_motive_2539_,
        v_a_2540_,
        v_t_2541_,
        v_h_2542_,
        v_arithShiftRight_2543_,
    );
    leanh::lean_dec(v_a_2540_);
    return v_res_2544_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(
    mut v_t_2545_: *mut leanh::LeanObject,
    mut v_var_2546_: *mut leanh::LeanObject,
    mut v_const_2547_: *mut leanh::LeanObject,
    mut v_extract_2548_: *mut leanh::LeanObject,
    mut v_bin_2549_: *mut leanh::LeanObject,
    mut v_un_2550_: *mut leanh::LeanObject,
    mut v_append_2551_: *mut leanh::LeanObject,
    mut v_replicate_2552_: *mut leanh::LeanObject,
    mut v_shiftLeft_2553_: *mut leanh::LeanObject,
    mut v_shiftRight_2554_: *mut leanh::LeanObject,
    mut v_arithShiftRight_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2545_) {
        0 => {
            let mut v_w_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            v_w_2556_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_w_2556_);
            v_idx_2557_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_idx_2557_);
            leanh::lean_dec_ref_known(v_t_2545_, 2);
            v___x_2558_ = leanh::lean_apply_2(v_var_2546_, v_w_2556_, v_idx_2557_);
            return v___x_2558_;
        }
        1 => {
            let mut v_w_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_var_2546_);
            v_w_2559_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_w_2559_);
            v_val_2560_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_val_2560_);
            leanh::lean_dec_ref_known(v_t_2545_, 2);
            v___x_2561_ = leanh::lean_apply_2(v_const_2547_, v_w_2559_, v_val_2560_);
            return v___x_2561_;
        }
        2 => {
            let mut v_w_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_len_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_w_2562_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_w_2562_);
            v_start_2563_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_start_2563_);
            v_len_2564_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc(v_len_2564_);
            v_expr_2565_ = leanh::lean_ctor_get(v_t_2545_, 3);
            leanh::lean_inc_ref(v_expr_2565_);
            leanh::lean_dec_ref_known(v_t_2545_, 4);
            v___x_2566_ = leanh::lean_apply_4(
                v_extract_2548_,
                v_w_2562_,
                v_start_2563_,
                v_len_2564_,
                v_expr_2565_,
            );
            return v___x_2566_;
        }
        3 => {
            let mut v_w_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_2569_: u8 = 0;
            let mut v_rhs_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_w_2567_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_w_2567_);
            v_lhs_2568_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc_ref(v_lhs_2568_);
            v_op_2569_ = leanh::lean_ctor_get_uint8(
                v_t_2545_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_2570_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc_ref(v_rhs_2570_);
            leanh::lean_dec_ref_known(v_t_2545_, 3);
            v___x_2571_ = leanh::lean_box((v_op_2569_) as usize);
            v___x_2572_ = leanh::lean_apply_4(
                v_bin_2549_,
                v_w_2567_,
                v_lhs_2568_,
                v___x_2571_,
                v_rhs_2570_,
            );
            return v___x_2572_;
        }
        4 => {
            let mut v_w_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_w_2573_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_w_2573_);
            v_op_2574_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_op_2574_);
            v_operand_2575_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc_ref(v_operand_2575_);
            leanh::lean_dec_ref_known(v_t_2545_, 3);
            v___x_2576_ =
                leanh::lean_apply_3(v_un_2550_, v_w_2573_, v_op_2574_, v_operand_2575_);
            return v___x_2576_;
        }
        5 => {
            let mut v_l_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_w_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_l_2577_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_l_2577_);
            v_r_2578_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_r_2578_);
            v_w_2579_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc(v_w_2579_);
            v_lhs_2580_ = leanh::lean_ctor_get(v_t_2545_, 3);
            leanh::lean_inc_ref(v_lhs_2580_);
            v_rhs_2581_ = leanh::lean_ctor_get(v_t_2545_, 4);
            leanh::lean_inc_ref(v_rhs_2581_);
            leanh::lean_dec_ref_known(v_t_2545_, 5);
            v___x_2582_ = leanh::lean_apply_6(
                v_append_2551_,
                v_l_2577_,
                v_r_2578_,
                v_w_2579_,
                v_lhs_2580_,
                v_rhs_2581_,
                leanh::lean_box(0),
            );
            return v___x_2582_;
        }
        6 => {
            let mut v_w_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_w_x27_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_w_2583_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_w_2583_);
            v_w_x27_2584_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_w_x27_2584_);
            v_n_2585_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc(v_n_2585_);
            v_expr_2586_ = leanh::lean_ctor_get(v_t_2545_, 3);
            leanh::lean_inc_ref(v_expr_2586_);
            leanh::lean_dec_ref_known(v_t_2545_, 4);
            v___x_2587_ = leanh::lean_apply_5(
                v_replicate_2552_,
                v_w_2583_,
                v_w_x27_2584_,
                v_n_2585_,
                v_expr_2586_,
                leanh::lean_box(0),
            );
            return v___x_2587_;
        }
        7 => {
            let mut v_m_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_m_2588_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_m_2588_);
            v_n_2589_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_n_2589_);
            v_lhs_2590_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc_ref(v_lhs_2590_);
            v_rhs_2591_ = leanh::lean_ctor_get(v_t_2545_, 3);
            leanh::lean_inc_ref(v_rhs_2591_);
            leanh::lean_dec_ref_known(v_t_2545_, 4);
            v___x_2592_ = leanh::lean_apply_4(
                v_shiftLeft_2553_,
                v_m_2588_,
                v_n_2589_,
                v_lhs_2590_,
                v_rhs_2591_,
            );
            return v___x_2592_;
        }
        8 => {
            let mut v_m_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2555_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_m_2593_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_m_2593_);
            v_n_2594_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_n_2594_);
            v_lhs_2595_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc_ref(v_lhs_2595_);
            v_rhs_2596_ = leanh::lean_ctor_get(v_t_2545_, 3);
            leanh::lean_inc_ref(v_rhs_2596_);
            leanh::lean_dec_ref_known(v_t_2545_, 4);
            v___x_2597_ = leanh::lean_apply_4(
                v_shiftRight_2554_,
                v_m_2593_,
                v_n_2594_,
                v_lhs_2595_,
                v_rhs_2596_,
            );
            return v___x_2597_;
        }
        _ => {
            let mut v_m_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_shiftRight_2554_);
            leanh::lean_dec(v_shiftLeft_2553_);
            leanh::lean_dec(v_replicate_2552_);
            leanh::lean_dec(v_append_2551_);
            leanh::lean_dec(v_un_2550_);
            leanh::lean_dec(v_bin_2549_);
            leanh::lean_dec(v_extract_2548_);
            leanh::lean_dec(v_const_2547_);
            leanh::lean_dec(v_var_2546_);
            v_m_2598_ = leanh::lean_ctor_get(v_t_2545_, 0);
            leanh::lean_inc(v_m_2598_);
            v_n_2599_ = leanh::lean_ctor_get(v_t_2545_, 1);
            leanh::lean_inc(v_n_2599_);
            v_lhs_2600_ = leanh::lean_ctor_get(v_t_2545_, 2);
            leanh::lean_inc_ref(v_lhs_2600_);
            v_rhs_2601_ = leanh::lean_ctor_get(v_t_2545_, 3);
            leanh::lean_inc_ref(v_rhs_2601_);
            leanh::lean_dec_ref_known(v_t_2545_, 4);
            v___x_2602_ = leanh::lean_apply_4(
                v_arithShiftRight_2555_,
                v_m_2598_,
                v_n_2599_,
                v_lhs_2600_,
                v_rhs_2601_,
            );
            return v___x_2602_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_casesOn___override(
    mut v_motive_2603_: *mut leanh::LeanObject,
    mut v_a_2604_: *mut leanh::LeanObject,
    mut v_t_2605_: *mut leanh::LeanObject,
    mut v_var_2606_: *mut leanh::LeanObject,
    mut v_const_2607_: *mut leanh::LeanObject,
    mut v_extract_2608_: *mut leanh::LeanObject,
    mut v_bin_2609_: *mut leanh::LeanObject,
    mut v_un_2610_: *mut leanh::LeanObject,
    mut v_append_2611_: *mut leanh::LeanObject,
    mut v_replicate_2612_: *mut leanh::LeanObject,
    mut v_shiftLeft_2613_: *mut leanh::LeanObject,
    mut v_shiftRight_2614_: *mut leanh::LeanObject,
    mut v_arithShiftRight_2615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2605_) {
        0 => {
            let mut v_w_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            v_w_2616_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_w_2616_);
            v_idx_2617_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_idx_2617_);
            leanh::lean_dec_ref_known(v_t_2605_, 2);
            v___x_2618_ = leanh::lean_apply_2(v_var_2606_, v_w_2616_, v_idx_2617_);
            return v___x_2618_;
        }
        1 => {
            let mut v_w_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_var_2606_);
            v_w_2619_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_w_2619_);
            v_val_2620_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_val_2620_);
            leanh::lean_dec_ref_known(v_t_2605_, 2);
            v___x_2621_ = leanh::lean_apply_2(v_const_2607_, v_w_2619_, v_val_2620_);
            return v___x_2621_;
        }
        2 => {
            let mut v_w_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_len_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_w_2622_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_w_2622_);
            v_start_2623_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_start_2623_);
            v_len_2624_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc(v_len_2624_);
            v_expr_2625_ = leanh::lean_ctor_get(v_t_2605_, 3);
            leanh::lean_inc_ref(v_expr_2625_);
            leanh::lean_dec_ref_known(v_t_2605_, 4);
            v___x_2626_ = leanh::lean_apply_4(
                v_extract_2608_,
                v_w_2622_,
                v_start_2623_,
                v_len_2624_,
                v_expr_2625_,
            );
            return v___x_2626_;
        }
        3 => {
            let mut v_w_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_2629_: u8 = 0;
            let mut v_rhs_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_w_2627_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_w_2627_);
            v_lhs_2628_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc_ref(v_lhs_2628_);
            v_op_2629_ = leanh::lean_ctor_get_uint8(
                v_t_2605_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_2630_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc_ref(v_rhs_2630_);
            leanh::lean_dec_ref_known(v_t_2605_, 3);
            v___x_2631_ = leanh::lean_box((v_op_2629_) as usize);
            v___x_2632_ = leanh::lean_apply_4(
                v_bin_2609_,
                v_w_2627_,
                v_lhs_2628_,
                v___x_2631_,
                v_rhs_2630_,
            );
            return v___x_2632_;
        }
        4 => {
            let mut v_w_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_w_2633_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_w_2633_);
            v_op_2634_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_op_2634_);
            v_operand_2635_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc_ref(v_operand_2635_);
            leanh::lean_dec_ref_known(v_t_2605_, 3);
            v___x_2636_ =
                leanh::lean_apply_3(v_un_2610_, v_w_2633_, v_op_2634_, v_operand_2635_);
            return v___x_2636_;
        }
        5 => {
            let mut v_l_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_w_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_l_2637_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_l_2637_);
            v_r_2638_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_r_2638_);
            v_w_2639_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc(v_w_2639_);
            v_lhs_2640_ = leanh::lean_ctor_get(v_t_2605_, 3);
            leanh::lean_inc_ref(v_lhs_2640_);
            v_rhs_2641_ = leanh::lean_ctor_get(v_t_2605_, 4);
            leanh::lean_inc_ref(v_rhs_2641_);
            leanh::lean_dec_ref_known(v_t_2605_, 5);
            v___x_2642_ = leanh::lean_apply_6(
                v_append_2611_,
                v_l_2637_,
                v_r_2638_,
                v_w_2639_,
                v_lhs_2640_,
                v_rhs_2641_,
                leanh::lean_box(0),
            );
            return v___x_2642_;
        }
        6 => {
            let mut v_w_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_w_x27_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_w_2643_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_w_2643_);
            v_w_x27_2644_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_w_x27_2644_);
            v_n_2645_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc(v_n_2645_);
            v_expr_2646_ = leanh::lean_ctor_get(v_t_2605_, 3);
            leanh::lean_inc_ref(v_expr_2646_);
            leanh::lean_dec_ref_known(v_t_2605_, 4);
            v___x_2647_ = leanh::lean_apply_5(
                v_replicate_2612_,
                v_w_2643_,
                v_w_x27_2644_,
                v_n_2645_,
                v_expr_2646_,
                leanh::lean_box(0),
            );
            return v___x_2647_;
        }
        7 => {
            let mut v_m_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_m_2648_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_m_2648_);
            v_n_2649_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_n_2649_);
            v_lhs_2650_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc_ref(v_lhs_2650_);
            v_rhs_2651_ = leanh::lean_ctor_get(v_t_2605_, 3);
            leanh::lean_inc_ref(v_rhs_2651_);
            leanh::lean_dec_ref_known(v_t_2605_, 4);
            v___x_2652_ = leanh::lean_apply_4(
                v_shiftLeft_2613_,
                v_m_2648_,
                v_n_2649_,
                v_lhs_2650_,
                v_rhs_2651_,
            );
            return v___x_2652_;
        }
        8 => {
            let mut v_m_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_arithShiftRight_2615_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_m_2653_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_m_2653_);
            v_n_2654_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_n_2654_);
            v_lhs_2655_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc_ref(v_lhs_2655_);
            v_rhs_2656_ = leanh::lean_ctor_get(v_t_2605_, 3);
            leanh::lean_inc_ref(v_rhs_2656_);
            leanh::lean_dec_ref_known(v_t_2605_, 4);
            v___x_2657_ = leanh::lean_apply_4(
                v_shiftRight_2614_,
                v_m_2653_,
                v_n_2654_,
                v_lhs_2655_,
                v_rhs_2656_,
            );
            return v___x_2657_;
        }
        _ => {
            let mut v_m_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_shiftRight_2614_);
            leanh::lean_dec(v_shiftLeft_2613_);
            leanh::lean_dec(v_replicate_2612_);
            leanh::lean_dec(v_append_2611_);
            leanh::lean_dec(v_un_2610_);
            leanh::lean_dec(v_bin_2609_);
            leanh::lean_dec(v_extract_2608_);
            leanh::lean_dec(v_const_2607_);
            leanh::lean_dec(v_var_2606_);
            v_m_2658_ = leanh::lean_ctor_get(v_t_2605_, 0);
            leanh::lean_inc(v_m_2658_);
            v_n_2659_ = leanh::lean_ctor_get(v_t_2605_, 1);
            leanh::lean_inc(v_n_2659_);
            v_lhs_2660_ = leanh::lean_ctor_get(v_t_2605_, 2);
            leanh::lean_inc_ref(v_lhs_2660_);
            v_rhs_2661_ = leanh::lean_ctor_get(v_t_2605_, 3);
            leanh::lean_inc_ref(v_rhs_2661_);
            leanh::lean_dec_ref_known(v_t_2605_, 4);
            v___x_2662_ = leanh::lean_apply_4(
                v_arithShiftRight_2615_,
                v_m_2658_,
                v_n_2659_,
                v_lhs_2660_,
                v_rhs_2661_,
            );
            return v___x_2662_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(
    mut v_motive_2663_: *mut leanh::LeanObject,
    mut v_a_2664_: *mut leanh::LeanObject,
    mut v_t_2665_: *mut leanh::LeanObject,
    mut v_var_2666_: *mut leanh::LeanObject,
    mut v_const_2667_: *mut leanh::LeanObject,
    mut v_extract_2668_: *mut leanh::LeanObject,
    mut v_bin_2669_: *mut leanh::LeanObject,
    mut v_un_2670_: *mut leanh::LeanObject,
    mut v_append_2671_: *mut leanh::LeanObject,
    mut v_replicate_2672_: *mut leanh::LeanObject,
    mut v_shiftLeft_2673_: *mut leanh::LeanObject,
    mut v_shiftRight_2674_: *mut leanh::LeanObject,
    mut v_arithShiftRight_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(
        v_motive_2663_,
        v_a_2664_,
        v_t_2665_,
        v_var_2666_,
        v_const_2667_,
        v_extract_2668_,
        v_bin_2669_,
        v_un_2670_,
        v_append_2671_,
        v_replicate_2672_,
        v_shiftLeft_2673_,
        v_shiftRight_2674_,
        v_arithShiftRight_2675_,
    );
    leanh::lean_dec(v_a_2664_);
    return v_res_2676_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_var___override(
    mut v_w_2677_: *mut leanh::LeanObject,
    mut v_idx_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2679_: u64 = 0;
    let mut v___x_2680_: u64 = 0;
    let mut v___x_2681_: u64 = 0;
    let mut v___x_2682_: u64 = 0;
    let mut v___x_2683_: u64 = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2679_ = 5u64;
    v___x_2680_ = lean_uint64_of_nat(v_w_2677_);
    v___x_2681_ = lean_uint64_of_nat(v_idx_2678_);
    v___x_2682_ = lean_uint64_mix_hash(v___x_2680_, v___x_2681_);
    v___x_2683_ = lean_uint64_mix_hash(v___x_2679_, v___x_2682_);
    v___x_2684_ = leanh::lean_alloc_ctor(0, 2, (8) as u32);
    leanh::lean_ctor_set(v___x_2684_, 0, v_w_2677_);
    leanh::lean_ctor_set(v___x_2684_, 1, v_idx_2678_);
    leanh::lean_ctor_set_uint64(
        v___x_2684_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_2683_,
    );
    return v___x_2684_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_const___override(
    mut v_w_2685_: *mut leanh::LeanObject,
    mut v_val_2686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2687_: u64 = 0;
    let mut v___x_2688_: u64 = 0;
    let mut v___x_2689_: u64 = 0;
    let mut v___x_2690_: u64 = 0;
    let mut v___x_2691_: u64 = 0;
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2687_ = 7u64;
    v___x_2688_ = lean_uint64_of_nat(v_w_2685_);
    v___x_2689_ = l_BitVec_hash(v_w_2685_, v_val_2686_);
    v___x_2690_ = lean_uint64_mix_hash(v___x_2688_, v___x_2689_);
    v___x_2691_ = lean_uint64_mix_hash(v___x_2687_, v___x_2690_);
    v___x_2692_ = leanh::lean_alloc_ctor(1, 2, (8) as u32);
    leanh::lean_ctor_set(v___x_2692_, 0, v_w_2685_);
    leanh::lean_ctor_set(v___x_2692_, 1, v_val_2686_);
    leanh::lean_ctor_set_uint64(
        v___x_2692_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_2691_,
    );
    return v___x_2692_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_extract___override(
    mut v_w_2693_: *mut leanh::LeanObject,
    mut v_start_2694_: *mut leanh::LeanObject,
    mut v_len_2695_: *mut leanh::LeanObject,
    mut v_expr_2696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2697_: u64 = 0;
    let mut v___x_2698_: u64 = 0;
    let mut v___x_2699_: u64 = 0;
    let mut v___y_2701_: u64 = 0;
    let mut v___x_2702_: u64 = 0;
    let mut v___x_2703_: u64 = 0;
    let mut v___x_2704_: u64 = 0;
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hashCode_2706_: u64 = 0;
    let mut v_hashCode_2707_: u64 = 0;
    let mut v_hashCode_2708_: u64 = 0;
    let mut v_hashCode_2709_: u64 = 0;
    let mut v_hashCode_2710_: u64 = 0;
    let mut v_hashCode_2711_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2697_ = 11u64;
                v___x_2698_ = lean_uint64_of_nat(v_start_2694_);
                v___x_2699_ = lean_uint64_of_nat(v_len_2695_);
                match leanh::lean_obj_tag(v_expr_2696_) {
                    0 => {
                        v_hashCode_2706_ = leanh::lean_ctor_get_uint64(
                            v_expr_2696_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2701_ = v_hashCode_2706_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_hashCode_2707_ = leanh::lean_ctor_get_uint64(
                            v_expr_2696_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2701_ = v_hashCode_2707_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_hashCode_2708_ = leanh::lean_ctor_get_uint64(
                            v_expr_2696_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2701_ = v_hashCode_2708_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_hashCode_2709_ = leanh::lean_ctor_get_uint64(
                            v_expr_2696_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2701_ = v_hashCode_2709_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_hashCode_2710_ = leanh::lean_ctor_get_uint64(
                            v_expr_2696_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2701_ = v_hashCode_2710_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_hashCode_2711_ = leanh::lean_ctor_get_uint64(
                            v_expr_2696_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2701_ = v_hashCode_2711_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2702_ = lean_uint64_mix_hash(v___x_2699_, v___y_2701_);
                v___x_2703_ = lean_uint64_mix_hash(v___x_2698_, v___x_2702_);
                v___x_2704_ = lean_uint64_mix_hash(v___x_2697_, v___x_2703_);
                v___x_2705_ = leanh::lean_alloc_ctor(2, 4, (8) as u32);
                leanh::lean_ctor_set(v___x_2705_, 0, v_w_2693_);
                leanh::lean_ctor_set(v___x_2705_, 1, v_start_2694_);
                leanh::lean_ctor_set(v___x_2705_, 2, v_len_2695_);
                leanh::lean_ctor_set(v___x_2705_, 3, v_expr_2696_);
                leanh::lean_ctor_set_uint64(
                    v___x_2705_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_2704_,
                );
                return v___x_2705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bin___override(
    mut v_w_2712_: *mut leanh::LeanObject,
    mut v_lhs_2713_: *mut leanh::LeanObject,
    mut v_op_2714_: u8,
    mut v_rhs_2715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2716_: u64 = 0;
    let mut v___x_2717_: u64 = 0;
    let mut v___y_2719_: u64 = 0;
    let mut v___y_2720_: u64 = 0;
    let mut v___y_2721_: u64 = 0;
    let mut v___x_2722_: u64 = 0;
    let mut v___x_2723_: u64 = 0;
    let mut v___x_2724_: u64 = 0;
    let mut v___x_2725_: u64 = 0;
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: u64 = 0;
    let mut v___x_2729_: u64 = 0;
    let mut v_hashCode_2730_: u64 = 0;
    let mut v_hashCode_2731_: u64 = 0;
    let mut v_hashCode_2732_: u64 = 0;
    let mut v_hashCode_2733_: u64 = 0;
    let mut v_hashCode_2734_: u64 = 0;
    let mut v_hashCode_2735_: u64 = 0;
    let mut v_hashCode_2736_: u64 = 0;
    let mut v_hashCode_2737_: u64 = 0;
    let mut v_hashCode_2738_: u64 = 0;
    let mut v_hashCode_2739_: u64 = 0;
    let mut v_hashCode_2740_: u64 = 0;
    let mut v_hashCode_2741_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2716_ = 13u64;
                v___x_2717_ = lean_uint64_of_nat(v_w_2712_);
                match leanh::lean_obj_tag(v_lhs_2713_) {
                    0 => {
                        v_hashCode_2736_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2713_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2728_ = v_hashCode_2736_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_hashCode_2737_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2713_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2728_ = v_hashCode_2737_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_hashCode_2738_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2713_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2728_ = v_hashCode_2738_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_hashCode_2739_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2713_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2728_ = v_hashCode_2739_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_hashCode_2740_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2713_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2728_ = v_hashCode_2740_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v_hashCode_2741_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2713_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2728_ = v_hashCode_2741_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2722_ = lean_uint64_mix_hash(v___y_2719_, v___y_2721_);
                v___x_2723_ = lean_uint64_mix_hash(v___y_2720_, v___x_2722_);
                v___x_2724_ = lean_uint64_mix_hash(v___x_2717_, v___x_2723_);
                v___x_2725_ = lean_uint64_mix_hash(v___x_2716_, v___x_2724_);
                v___x_2726_ = leanh::lean_alloc_ctor(3, 3, (9) as u32);
                leanh::lean_ctor_set(v___x_2726_, 0, v_w_2712_);
                leanh::lean_ctor_set(v___x_2726_, 1, v_lhs_2713_);
                leanh::lean_ctor_set(v___x_2726_, 2, v_rhs_2715_);
                leanh::lean_ctor_set_uint64(
                    v___x_2726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2725_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v_op_2714_,
                );
                return v___x_2726_;
            }
            2 => {
                v___x_2729_ = l_Std_Tactic_BVDecide_instHashableBVBinOp_hash(v_op_2714_);
                match leanh::lean_obj_tag(v_rhs_2715_) {
                    0 => {
                        v_hashCode_2730_ = leanh::lean_ctor_get_uint64(
                            v_rhs_2715_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2719_ = v___x_2729_;
                        v___y_2720_ = v___y_2728_;
                        v___y_2721_ = v_hashCode_2730_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_hashCode_2731_ = leanh::lean_ctor_get_uint64(
                            v_rhs_2715_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2719_ = v___x_2729_;
                        v___y_2720_ = v___y_2728_;
                        v___y_2721_ = v_hashCode_2731_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_hashCode_2732_ = leanh::lean_ctor_get_uint64(
                            v_rhs_2715_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2719_ = v___x_2729_;
                        v___y_2720_ = v___y_2728_;
                        v___y_2721_ = v_hashCode_2732_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_hashCode_2733_ = leanh::lean_ctor_get_uint64(
                            v_rhs_2715_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2719_ = v___x_2729_;
                        v___y_2720_ = v___y_2728_;
                        v___y_2721_ = v_hashCode_2733_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_hashCode_2734_ = leanh::lean_ctor_get_uint64(
                            v_rhs_2715_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2719_ = v___x_2729_;
                        v___y_2720_ = v___y_2728_;
                        v___y_2721_ = v_hashCode_2734_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_hashCode_2735_ = leanh::lean_ctor_get_uint64(
                            v_rhs_2715_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2719_ = v___x_2729_;
                        v___y_2720_ = v___y_2728_;
                        v___y_2721_ = v_hashCode_2735_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(
    mut v_w_2742_: *mut leanh::LeanObject,
    mut v_lhs_2743_: *mut leanh::LeanObject,
    mut v_op_2744_: *mut leanh::LeanObject,
    mut v_rhs_2745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_boxed_2746_: u8 = 0;
    let mut v_res_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_op_boxed_2746_ = (leanh::lean_unbox(v_op_2744_) as u8);
    v_res_2747_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(
        v_w_2742_,
        v_lhs_2743_,
        v_op_boxed_2746_,
        v_rhs_2745_,
    );
    return v_res_2747_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_un___override(
    mut v_w_2748_: *mut leanh::LeanObject,
    mut v_op_2749_: *mut leanh::LeanObject,
    mut v_operand_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2751_: u64 = 0;
    let mut v___x_2752_: u64 = 0;
    let mut v___x_2753_: u64 = 0;
    let mut v___y_2755_: u64 = 0;
    let mut v___x_2756_: u64 = 0;
    let mut v___x_2757_: u64 = 0;
    let mut v___x_2758_: u64 = 0;
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hashCode_2760_: u64 = 0;
    let mut v_hashCode_2761_: u64 = 0;
    let mut v_hashCode_2762_: u64 = 0;
    let mut v_hashCode_2763_: u64 = 0;
    let mut v_hashCode_2764_: u64 = 0;
    let mut v_hashCode_2765_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2751_ = 17u64;
                v___x_2752_ = lean_uint64_of_nat(v_w_2748_);
                v___x_2753_ = l_Std_Tactic_BVDecide_instHashableBVUnOp_hash(v_op_2749_);
                match leanh::lean_obj_tag(v_operand_2750_) {
                    0 => {
                        v_hashCode_2760_ = leanh::lean_ctor_get_uint64(
                            v_operand_2750_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2755_ = v_hashCode_2760_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_hashCode_2761_ = leanh::lean_ctor_get_uint64(
                            v_operand_2750_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2755_ = v_hashCode_2761_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_hashCode_2762_ = leanh::lean_ctor_get_uint64(
                            v_operand_2750_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2755_ = v_hashCode_2762_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_hashCode_2763_ = leanh::lean_ctor_get_uint64(
                            v_operand_2750_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2755_ = v_hashCode_2763_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_hashCode_2764_ = leanh::lean_ctor_get_uint64(
                            v_operand_2750_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2755_ = v_hashCode_2764_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_hashCode_2765_ = leanh::lean_ctor_get_uint64(
                            v_operand_2750_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2755_ = v_hashCode_2765_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2756_ = lean_uint64_mix_hash(v___x_2753_, v___y_2755_);
                v___x_2757_ = lean_uint64_mix_hash(v___x_2752_, v___x_2756_);
                v___x_2758_ = lean_uint64_mix_hash(v___x_2751_, v___x_2757_);
                v___x_2759_ = leanh::lean_alloc_ctor(4, 3, (8) as u32);
                leanh::lean_ctor_set(v___x_2759_, 0, v_w_2748_);
                leanh::lean_ctor_set(v___x_2759_, 1, v_op_2749_);
                leanh::lean_ctor_set(v___x_2759_, 2, v_operand_2750_);
                leanh::lean_ctor_set_uint64(
                    v___x_2759_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2758_,
                );
                return v___x_2759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(
    mut v_l_2766_: *mut leanh::LeanObject,
    mut v_r_2767_: *mut leanh::LeanObject,
    mut v_w_2768_: *mut leanh::LeanObject,
    mut v_lhs_2769_: *mut leanh::LeanObject,
    mut v_rhs_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2771_: u64 = 0;
    let mut v___x_2772_: u64 = 0;
    let mut v___y_2774_: u64 = 0;
    let mut v___y_2775_: u64 = 0;
    let mut v___x_2776_: u64 = 0;
    let mut v___x_2777_: u64 = 0;
    let mut v___x_2778_: u64 = 0;
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: u64 = 0;
    let mut v_hashCode_2782_: u64 = 0;
    let mut v_hashCode_2783_: u64 = 0;
    let mut v_hashCode_2784_: u64 = 0;
    let mut v_hashCode_2785_: u64 = 0;
    let mut v_hashCode_2786_: u64 = 0;
    let mut v_hashCode_2787_: u64 = 0;
    let mut v_hashCode_2788_: u64 = 0;
    let mut v_hashCode_2789_: u64 = 0;
    let mut v_hashCode_2790_: u64 = 0;
    let mut v_hashCode_2791_: u64 = 0;
    let mut v_hashCode_2792_: u64 = 0;
    let mut v_hashCode_2793_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2771_ = 19u64;
                v___x_2772_ = lean_uint64_of_nat(v_w_2768_);
                match leanh::lean_obj_tag(v_lhs_2769_) {
                    0 => {
                        v_hashCode_2788_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2769_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2781_ = v_hashCode_2788_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_hashCode_2789_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2769_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2781_ = v_hashCode_2789_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_hashCode_2790_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2769_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2781_ = v_hashCode_2790_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_hashCode_2791_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2769_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2781_ = v_hashCode_2791_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_hashCode_2792_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2769_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2781_ = v_hashCode_2792_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v_hashCode_2793_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2769_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2781_ = v_hashCode_2793_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2776_ = lean_uint64_mix_hash(v___y_2774_, v___y_2775_);
                v___x_2777_ = lean_uint64_mix_hash(v___x_2772_, v___x_2776_);
                v___x_2778_ = lean_uint64_mix_hash(v___x_2771_, v___x_2777_);
                v___x_2779_ = leanh::lean_alloc_ctor(5, 5, (8) as u32);
                leanh::lean_ctor_set(v___x_2779_, 0, v_l_2766_);
                leanh::lean_ctor_set(v___x_2779_, 1, v_r_2767_);
                leanh::lean_ctor_set(v___x_2779_, 2, v_w_2768_);
                leanh::lean_ctor_set(v___x_2779_, 3, v_lhs_2769_);
                leanh::lean_ctor_set(v___x_2779_, 4, v_rhs_2770_);
                leanh::lean_ctor_set_uint64(
                    v___x_2779_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___x_2778_,
                );
                return v___x_2779_;
            }
            2 => match leanh::lean_obj_tag(v_rhs_2770_) {
                0 => {
                    v_hashCode_2782_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2770_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2774_ = v___y_2781_;
                    v___y_2775_ = v_hashCode_2782_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_hashCode_2783_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2770_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2774_ = v___y_2781_;
                    v___y_2775_ = v_hashCode_2783_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_hashCode_2784_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2770_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2774_ = v___y_2781_;
                    v___y_2775_ = v_hashCode_2784_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_hashCode_2785_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2770_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2774_ = v___y_2781_;
                    v___y_2775_ = v_hashCode_2785_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_hashCode_2786_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2770_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    v___y_2774_ = v___y_2781_;
                    v___y_2775_ = v_hashCode_2786_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_hashCode_2787_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2770_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v___y_2774_ = v___y_2781_;
                    v___y_2775_ = v_hashCode_2787_;
                    state = 1;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_append___override(
    mut v_l_2794_: *mut leanh::LeanObject,
    mut v_r_2795_: *mut leanh::LeanObject,
    mut v_w_2796_: *mut leanh::LeanObject,
    mut v_lhs_2797_: *mut leanh::LeanObject,
    mut v_rhs_2798_: *mut leanh::LeanObject,
    mut v_h_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2800_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(
        v_l_2794_,
        v_r_2795_,
        v_w_2796_,
        v_lhs_2797_,
        v_rhs_2798_,
    );
    return v___x_2800_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(
    mut v_w_2801_: *mut leanh::LeanObject,
    mut v_w_x27_2802_: *mut leanh::LeanObject,
    mut v_n_2803_: *mut leanh::LeanObject,
    mut v_expr_2804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2805_: u64 = 0;
    let mut v___x_2806_: u64 = 0;
    let mut v___x_2807_: u64 = 0;
    let mut v___y_2809_: u64 = 0;
    let mut v___x_2810_: u64 = 0;
    let mut v___x_2811_: u64 = 0;
    let mut v___x_2812_: u64 = 0;
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hashCode_2814_: u64 = 0;
    let mut v_hashCode_2815_: u64 = 0;
    let mut v_hashCode_2816_: u64 = 0;
    let mut v_hashCode_2817_: u64 = 0;
    let mut v_hashCode_2818_: u64 = 0;
    let mut v_hashCode_2819_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2805_ = 23u64;
                v___x_2806_ = lean_uint64_of_nat(v_w_x27_2802_);
                v___x_2807_ = lean_uint64_of_nat(v_n_2803_);
                match leanh::lean_obj_tag(v_expr_2804_) {
                    0 => {
                        v_hashCode_2814_ = leanh::lean_ctor_get_uint64(
                            v_expr_2804_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2809_ = v_hashCode_2814_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v_hashCode_2815_ = leanh::lean_ctor_get_uint64(
                            v_expr_2804_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2809_ = v_hashCode_2815_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_hashCode_2816_ = leanh::lean_ctor_get_uint64(
                            v_expr_2804_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2809_ = v_hashCode_2816_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_hashCode_2817_ = leanh::lean_ctor_get_uint64(
                            v_expr_2804_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2809_ = v_hashCode_2817_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_hashCode_2818_ = leanh::lean_ctor_get_uint64(
                            v_expr_2804_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2809_ = v_hashCode_2818_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v_hashCode_2819_ = leanh::lean_ctor_get_uint64(
                            v_expr_2804_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2809_ = v_hashCode_2819_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2810_ = lean_uint64_mix_hash(v___x_2807_, v___y_2809_);
                v___x_2811_ = lean_uint64_mix_hash(v___x_2806_, v___x_2810_);
                v___x_2812_ = lean_uint64_mix_hash(v___x_2805_, v___x_2811_);
                v___x_2813_ = leanh::lean_alloc_ctor(6, 4, (8) as u32);
                leanh::lean_ctor_set(v___x_2813_, 0, v_w_2801_);
                leanh::lean_ctor_set(v___x_2813_, 1, v_w_x27_2802_);
                leanh::lean_ctor_set(v___x_2813_, 2, v_n_2803_);
                leanh::lean_ctor_set(v___x_2813_, 3, v_expr_2804_);
                leanh::lean_ctor_set_uint64(
                    v___x_2813_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_2812_,
                );
                return v___x_2813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_replicate___override(
    mut v_w_2820_: *mut leanh::LeanObject,
    mut v_w_x27_2821_: *mut leanh::LeanObject,
    mut v_n_2822_: *mut leanh::LeanObject,
    mut v_expr_2823_: *mut leanh::LeanObject,
    mut v_h_2824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2825_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(
        v_w_2820_,
        v_w_x27_2821_,
        v_n_2822_,
        v_expr_2823_,
    );
    return v___x_2825_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(
    mut v_m_2826_: *mut leanh::LeanObject,
    mut v_n_2827_: *mut leanh::LeanObject,
    mut v_lhs_2828_: *mut leanh::LeanObject,
    mut v_rhs_2829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2830_: u64 = 0;
    let mut v___x_2831_: u64 = 0;
    let mut v___y_2833_: u64 = 0;
    let mut v___y_2834_: u64 = 0;
    let mut v___x_2835_: u64 = 0;
    let mut v___x_2836_: u64 = 0;
    let mut v___x_2837_: u64 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2840_: u64 = 0;
    let mut v_hashCode_2841_: u64 = 0;
    let mut v_hashCode_2842_: u64 = 0;
    let mut v_hashCode_2843_: u64 = 0;
    let mut v_hashCode_2844_: u64 = 0;
    let mut v_hashCode_2845_: u64 = 0;
    let mut v_hashCode_2846_: u64 = 0;
    let mut v_hashCode_2847_: u64 = 0;
    let mut v_hashCode_2848_: u64 = 0;
    let mut v_hashCode_2849_: u64 = 0;
    let mut v_hashCode_2850_: u64 = 0;
    let mut v_hashCode_2851_: u64 = 0;
    let mut v_hashCode_2852_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2830_ = 29u64;
                v___x_2831_ = lean_uint64_of_nat(v_m_2826_);
                match leanh::lean_obj_tag(v_lhs_2828_) {
                    0 => {
                        v_hashCode_2847_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2828_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2840_ = v_hashCode_2847_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_hashCode_2848_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2828_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2840_ = v_hashCode_2848_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_hashCode_2849_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2828_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2840_ = v_hashCode_2849_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_hashCode_2850_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2828_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2840_ = v_hashCode_2850_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_hashCode_2851_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2828_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2840_ = v_hashCode_2851_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v_hashCode_2852_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2828_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2840_ = v_hashCode_2852_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2835_ = lean_uint64_mix_hash(v___y_2833_, v___y_2834_);
                v___x_2836_ = lean_uint64_mix_hash(v___x_2831_, v___x_2835_);
                v___x_2837_ = lean_uint64_mix_hash(v___x_2830_, v___x_2836_);
                v___x_2838_ = leanh::lean_alloc_ctor(7, 4, (8) as u32);
                leanh::lean_ctor_set(v___x_2838_, 0, v_m_2826_);
                leanh::lean_ctor_set(v___x_2838_, 1, v_n_2827_);
                leanh::lean_ctor_set(v___x_2838_, 2, v_lhs_2828_);
                leanh::lean_ctor_set(v___x_2838_, 3, v_rhs_2829_);
                leanh::lean_ctor_set_uint64(
                    v___x_2838_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_2837_,
                );
                return v___x_2838_;
            }
            2 => match leanh::lean_obj_tag(v_rhs_2829_) {
                0 => {
                    v_hashCode_2841_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2829_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2833_ = v___y_2840_;
                    v___y_2834_ = v_hashCode_2841_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_hashCode_2842_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2829_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2833_ = v___y_2840_;
                    v___y_2834_ = v_hashCode_2842_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_hashCode_2843_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2829_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2833_ = v___y_2840_;
                    v___y_2834_ = v_hashCode_2843_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_hashCode_2844_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2829_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2833_ = v___y_2840_;
                    v___y_2834_ = v_hashCode_2844_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_hashCode_2845_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2829_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    v___y_2833_ = v___y_2840_;
                    v___y_2834_ = v_hashCode_2845_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_hashCode_2846_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2829_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v___y_2833_ = v___y_2840_;
                    v___y_2834_ = v_hashCode_2846_;
                    state = 1;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(
    mut v_m_2853_: *mut leanh::LeanObject,
    mut v_n_2854_: *mut leanh::LeanObject,
    mut v_lhs_2855_: *mut leanh::LeanObject,
    mut v_rhs_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2857_: u64 = 0;
    let mut v___x_2858_: u64 = 0;
    let mut v___y_2860_: u64 = 0;
    let mut v___y_2861_: u64 = 0;
    let mut v___x_2862_: u64 = 0;
    let mut v___x_2863_: u64 = 0;
    let mut v___x_2864_: u64 = 0;
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: u64 = 0;
    let mut v_hashCode_2868_: u64 = 0;
    let mut v_hashCode_2869_: u64 = 0;
    let mut v_hashCode_2870_: u64 = 0;
    let mut v_hashCode_2871_: u64 = 0;
    let mut v_hashCode_2872_: u64 = 0;
    let mut v_hashCode_2873_: u64 = 0;
    let mut v_hashCode_2874_: u64 = 0;
    let mut v_hashCode_2875_: u64 = 0;
    let mut v_hashCode_2876_: u64 = 0;
    let mut v_hashCode_2877_: u64 = 0;
    let mut v_hashCode_2878_: u64 = 0;
    let mut v_hashCode_2879_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2857_ = 31u64;
                v___x_2858_ = lean_uint64_of_nat(v_m_2853_);
                match leanh::lean_obj_tag(v_lhs_2855_) {
                    0 => {
                        v_hashCode_2874_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2855_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2867_ = v_hashCode_2874_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_hashCode_2875_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2855_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2867_ = v_hashCode_2875_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_hashCode_2876_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2855_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2867_ = v_hashCode_2876_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_hashCode_2877_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2855_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2867_ = v_hashCode_2877_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_hashCode_2878_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2855_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2867_ = v_hashCode_2878_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v_hashCode_2879_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2855_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2867_ = v_hashCode_2879_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2862_ = lean_uint64_mix_hash(v___y_2860_, v___y_2861_);
                v___x_2863_ = lean_uint64_mix_hash(v___x_2858_, v___x_2862_);
                v___x_2864_ = lean_uint64_mix_hash(v___x_2857_, v___x_2863_);
                v___x_2865_ = leanh::lean_alloc_ctor(8, 4, (8) as u32);
                leanh::lean_ctor_set(v___x_2865_, 0, v_m_2853_);
                leanh::lean_ctor_set(v___x_2865_, 1, v_n_2854_);
                leanh::lean_ctor_set(v___x_2865_, 2, v_lhs_2855_);
                leanh::lean_ctor_set(v___x_2865_, 3, v_rhs_2856_);
                leanh::lean_ctor_set_uint64(
                    v___x_2865_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_2864_,
                );
                return v___x_2865_;
            }
            2 => match leanh::lean_obj_tag(v_rhs_2856_) {
                0 => {
                    v_hashCode_2868_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2856_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2860_ = v___y_2867_;
                    v___y_2861_ = v_hashCode_2868_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_hashCode_2869_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2856_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2860_ = v___y_2867_;
                    v___y_2861_ = v_hashCode_2869_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_hashCode_2870_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2856_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2860_ = v___y_2867_;
                    v___y_2861_ = v_hashCode_2870_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_hashCode_2871_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2856_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2860_ = v___y_2867_;
                    v___y_2861_ = v_hashCode_2871_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_hashCode_2872_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2856_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    v___y_2860_ = v___y_2867_;
                    v___y_2861_ = v_hashCode_2872_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_hashCode_2873_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2856_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v___y_2860_ = v___y_2867_;
                    v___y_2861_ = v_hashCode_2873_;
                    state = 1;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(
    mut v_m_2880_: *mut leanh::LeanObject,
    mut v_n_2881_: *mut leanh::LeanObject,
    mut v_lhs_2882_: *mut leanh::LeanObject,
    mut v_rhs_2883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2884_: u64 = 0;
    let mut v___x_2885_: u64 = 0;
    let mut v___y_2887_: u64 = 0;
    let mut v___y_2888_: u64 = 0;
    let mut v___x_2889_: u64 = 0;
    let mut v___x_2890_: u64 = 0;
    let mut v___x_2891_: u64 = 0;
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2894_: u64 = 0;
    let mut v_hashCode_2895_: u64 = 0;
    let mut v_hashCode_2896_: u64 = 0;
    let mut v_hashCode_2897_: u64 = 0;
    let mut v_hashCode_2898_: u64 = 0;
    let mut v_hashCode_2899_: u64 = 0;
    let mut v_hashCode_2900_: u64 = 0;
    let mut v_hashCode_2901_: u64 = 0;
    let mut v_hashCode_2902_: u64 = 0;
    let mut v_hashCode_2903_: u64 = 0;
    let mut v_hashCode_2904_: u64 = 0;
    let mut v_hashCode_2905_: u64 = 0;
    let mut v_hashCode_2906_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2884_ = 37u64;
                v___x_2885_ = lean_uint64_of_nat(v_m_2880_);
                match leanh::lean_obj_tag(v_lhs_2882_) {
                    0 => {
                        v_hashCode_2901_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2882_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2894_ = v_hashCode_2901_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_hashCode_2902_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2882_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2894_ = v_hashCode_2902_;
                        state = 2;
                        continue;
                    }
                    3 => {
                        v_hashCode_2903_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2882_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2894_ = v_hashCode_2903_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_hashCode_2904_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2882_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        );
                        v___y_2894_ = v_hashCode_2904_;
                        state = 2;
                        continue;
                    }
                    5 => {
                        v_hashCode_2905_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2882_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                        );
                        v___y_2894_ = v_hashCode_2905_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        v_hashCode_2906_ = leanh::lean_ctor_get_uint64(
                            v_lhs_2882_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        );
                        v___y_2894_ = v_hashCode_2906_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2889_ = lean_uint64_mix_hash(v___y_2887_, v___y_2888_);
                v___x_2890_ = lean_uint64_mix_hash(v___x_2885_, v___x_2889_);
                v___x_2891_ = lean_uint64_mix_hash(v___x_2884_, v___x_2890_);
                v___x_2892_ = leanh::lean_alloc_ctor(9, 4, (8) as u32);
                leanh::lean_ctor_set(v___x_2892_, 0, v_m_2880_);
                leanh::lean_ctor_set(v___x_2892_, 1, v_n_2881_);
                leanh::lean_ctor_set(v___x_2892_, 2, v_lhs_2882_);
                leanh::lean_ctor_set(v___x_2892_, 3, v_rhs_2883_);
                leanh::lean_ctor_set_uint64(
                    v___x_2892_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___x_2891_,
                );
                return v___x_2892_;
            }
            2 => match leanh::lean_obj_tag(v_rhs_2883_) {
                0 => {
                    v_hashCode_2895_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2883_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2887_ = v___y_2894_;
                    v___y_2888_ = v_hashCode_2895_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_hashCode_2896_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2883_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2887_ = v___y_2894_;
                    v___y_2888_ = v_hashCode_2896_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_hashCode_2897_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2883_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2887_ = v___y_2894_;
                    v___y_2888_ = v_hashCode_2897_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_hashCode_2898_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2883_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2887_ = v___y_2894_;
                    v___y_2888_ = v_hashCode_2898_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_hashCode_2899_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2883_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    v___y_2887_ = v___y_2894_;
                    v___y_2888_ = v_hashCode_2899_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_hashCode_2900_ = leanh::lean_ctor_get_uint64(
                        v_rhs_2883_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v___y_2887_ = v___y_2894_;
                    v___y_2888_ = v_hashCode_2900_;
                    state = 1;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(
    mut v_x_2907_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_x_2907_) {
        0 => {
            let mut v_hashCode_2908_: u64 = 0;
            v_hashCode_2908_ = leanh::lean_ctor_get_uint64(
                v_x_2907_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_2908_;
        }
        1 => {
            let mut v_hashCode_2909_: u64 = 0;
            v_hashCode_2909_ = leanh::lean_ctor_get_uint64(
                v_x_2907_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_2909_;
        }
        3 => {
            let mut v_hashCode_2910_: u64 = 0;
            v_hashCode_2910_ = leanh::lean_ctor_get_uint64(
                v_x_2907_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_2910_;
        }
        4 => {
            let mut v_hashCode_2911_: u64 = 0;
            v_hashCode_2911_ = leanh::lean_ctor_get_uint64(
                v_x_2907_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_2911_;
        }
        5 => {
            let mut v_hashCode_2912_: u64 = 0;
            v_hashCode_2912_ = leanh::lean_ctor_get_uint64(
                v_x_2907_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
            );
            return v_hashCode_2912_;
        }
        _ => {
            let mut v_hashCode_2913_: u64 = 0;
            v_hashCode_2913_ = leanh::lean_ctor_get_uint64(
                v_x_2907_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            return v_hashCode_2913_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(
    mut v_x_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2915_: u64 = 0;
    let mut v_r_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2915_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(v_x_2914_);
    leanh::lean_dec_ref(v_x_2914_);
    v_r_2916_ = leanh::lean_box_uint64(v_res_2915_);
    return v_r_2916_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_hashCode___override(
    mut v_a_2917_: *mut leanh::LeanObject,
    mut v_x_2918_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_x_2918_) {
        0 => {
            let mut v_hashCode_2919_: u64 = 0;
            v_hashCode_2919_ = leanh::lean_ctor_get_uint64(
                v_x_2918_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_2919_;
        }
        1 => {
            let mut v_hashCode_2920_: u64 = 0;
            v_hashCode_2920_ = leanh::lean_ctor_get_uint64(
                v_x_2918_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_2920_;
        }
        3 => {
            let mut v_hashCode_2921_: u64 = 0;
            v_hashCode_2921_ = leanh::lean_ctor_get_uint64(
                v_x_2918_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_2921_;
        }
        4 => {
            let mut v_hashCode_2922_: u64 = 0;
            v_hashCode_2922_ = leanh::lean_ctor_get_uint64(
                v_x_2918_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_2922_;
        }
        5 => {
            let mut v_hashCode_2923_: u64 = 0;
            v_hashCode_2923_ = leanh::lean_ctor_get_uint64(
                v_x_2918_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
            );
            return v_hashCode_2923_;
        }
        _ => {
            let mut v_hashCode_2924_: u64 = 0;
            v_hashCode_2924_ = leanh::lean_ctor_get_uint64(
                v_x_2918_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            return v_hashCode_2924_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(
    mut v_a_2925_: *mut leanh::LeanObject,
    mut v_x_2926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2927_: u64 = 0;
    let mut v_r_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2927_ = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(v_a_2925_, v_x_2926_);
    leanh::lean_dec_ref(v_x_2926_);
    leanh::lean_dec(v_a_2925_);
    v_r_2928_ = leanh::lean_box_uint64(v_res_2927_);
    return v_r_2928_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(
    mut v_expr_2929_: *mut leanh::LeanObject,
) -> u64 {
    match leanh::lean_obj_tag(v_expr_2929_) {
        0 => {
            let mut v_hashCode_2930_: u64 = 0;
            v_hashCode_2930_ = leanh::lean_ctor_get_uint64(
                v_expr_2929_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_2930_;
        }
        1 => {
            let mut v_hashCode_2931_: u64 = 0;
            v_hashCode_2931_ = leanh::lean_ctor_get_uint64(
                v_expr_2929_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_hashCode_2931_;
        }
        3 => {
            let mut v_hashCode_2932_: u64 = 0;
            v_hashCode_2932_ = leanh::lean_ctor_get_uint64(
                v_expr_2929_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_2932_;
        }
        4 => {
            let mut v_hashCode_2933_: u64 = 0;
            v_hashCode_2933_ = leanh::lean_ctor_get_uint64(
                v_expr_2929_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            );
            return v_hashCode_2933_;
        }
        5 => {
            let mut v_hashCode_2934_: u64 = 0;
            v_hashCode_2934_ = leanh::lean_ctor_get_uint64(
                v_expr_2929_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
            );
            return v_hashCode_2934_;
        }
        _ => {
            let mut v_hashCode_2935_: u64 = 0;
            v_hashCode_2935_ = leanh::lean_ctor_get_uint64(
                v_expr_2929_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
            );
            return v_hashCode_2935_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(
    mut v_expr_2936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2937_: u64 = 0;
    let mut v_r_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2937_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(v_expr_2936_);
    leanh::lean_dec_ref(v_expr_2936_);
    v_r_2938_ = leanh::lean_box_uint64(v_res_2937_);
    return v_r_2938_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_instHashable(
    mut v_w_2940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2941_ = l_Std_Tactic_BVDecide_BVExpr_instHashable___closed__0;
    return v___f_2941_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(
    mut v_w_2942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2943_ = l_Std_Tactic_BVDecide_BVExpr_instHashable(v_w_2942_);
    leanh::lean_dec(v_w_2942_);
    return v_res_2943_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(
    mut v_l_2944_: *mut leanh::LeanObject,
    mut v_r_2945_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2946_: usize = 0;
    let mut v___x_2947_: usize = 0;
    let mut v___x_2948_: u8 = 0;
    let mut v___y_2950_: u64 = 0;
    let mut v___y_2951_: u64 = 0;
    let mut v___x_2952_: u8 = 0;
    let mut v_idx_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    let mut v_val_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u8 = 0;
    let mut v_w_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: u8 = 0;
    let mut v_lhs_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2969_: u8 = 0;
    let mut v_rhs_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2972_: u8 = 0;
    let mut v_rhs_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    let mut v___x_2975_: u8 = 0;
    let mut v_op_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_operand_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_operand_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v_l_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: u8 = 0;
    let mut v___x_2993_: u8 = 0;
    let mut v_w_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_w_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: u8 = 0;
    let mut v___x_3002_: u8 = 0;
    let mut v_n_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: u8 = 0;
    let mut v___x_3011_: u8 = 0;
    let mut v_n_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: u8 = 0;
    let mut v_n_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: u8 = 0;
    let mut v___y_3032_: u64 = 0;
    let mut v_hashCode_3033_: u64 = 0;
    let mut v_hashCode_3034_: u64 = 0;
    let mut v_hashCode_3035_: u64 = 0;
    let mut v_hashCode_3036_: u64 = 0;
    let mut v_hashCode_3037_: u64 = 0;
    let mut v_hashCode_3038_: u64 = 0;
    let mut v_hashCode_3039_: u64 = 0;
    let mut v_hashCode_3040_: u64 = 0;
    let mut v_hashCode_3041_: u64 = 0;
    let mut v_hashCode_3042_: u64 = 0;
    let mut v_hashCode_3043_: u64 = 0;
    let mut v_hashCode_3044_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2946_ = lean_ptr_addr(v_l_2944_);
                v___x_2947_ = lean_ptr_addr(v_r_2945_);
                v___x_2948_ = lean_usize_dec_eq(v___x_2946_, v___x_2947_);
                if v___x_2948_ == 0 {
                    match leanh::lean_obj_tag(v_l_2944_) {
                        0 => {
                            v_hashCode_3039_ = leanh::lean_ctor_get_uint64(
                                v_l_2944_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            );
                            v___y_3032_ = v_hashCode_3039_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_hashCode_3040_ = leanh::lean_ctor_get_uint64(
                                v_l_2944_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            );
                            v___y_3032_ = v_hashCode_3040_;
                            state = 2;
                            continue;
                        }
                        3 => {
                            v_hashCode_3041_ = leanh::lean_ctor_get_uint64(
                                v_l_2944_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                            );
                            v___y_3032_ = v_hashCode_3041_;
                            state = 2;
                            continue;
                        }
                        4 => {
                            v_hashCode_3042_ = leanh::lean_ctor_get_uint64(
                                v_l_2944_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                            );
                            v___y_3032_ = v_hashCode_3042_;
                            state = 2;
                            continue;
                        }
                        5 => {
                            v_hashCode_3043_ = leanh::lean_ctor_get_uint64(
                                v_l_2944_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                            );
                            v___y_3032_ = v_hashCode_3043_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_hashCode_3044_ = leanh::lean_ctor_get_uint64(
                                v_l_2944_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                            );
                            v___y_3032_ = v_hashCode_3044_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    return v___x_2948_;
                }
            }
            1 => {
                v___x_2952_ = lean_uint64_dec_eq(v___y_2950_, v___y_2951_);
                if v___x_2952_ == 0 {
                    return v___x_2948_;
                } else {
                    if v___x_2948_ == 0 {
                        match leanh::lean_obj_tag(v_l_2944_) {
                            0 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 0 {
                                    v_idx_2953_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_idx_2954_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v___x_2955_ = lean_nat_dec_eq(v_idx_2953_, v_idx_2954_);
                                    return v___x_2955_;
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            1 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 1 {
                                    v_val_2956_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_val_2957_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v___x_2958_ = lean_nat_dec_eq(v_val_2956_, v_val_2957_);
                                    return v___x_2958_;
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            2 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 2 {
                                    v_w_2959_ = leanh::lean_ctor_get(v_l_2944_, 0);
                                    v_start_2960_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_expr_2961_ = leanh::lean_ctor_get(v_l_2944_, 3);
                                    v_w_2962_ = leanh::lean_ctor_get(v_r_2945_, 0);
                                    v_start_2963_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v_expr_2964_ = leanh::lean_ctor_get(v_r_2945_, 3);
                                    v___x_2965_ = lean_nat_dec_eq(v_w_2959_, v_w_2962_);
                                    if v___x_2965_ == 0 {
                                        return v___x_2965_;
                                    } else {
                                        v___x_2966_ = lean_nat_dec_eq(v_start_2960_, v_start_2963_);
                                        if v___x_2966_ == 0 {
                                            return v___x_2966_;
                                        } else {
                                            v_l_2944_ = v_expr_2961_;
                                            v_r_2945_ = v_expr_2964_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            3 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 3 {
                                    v_lhs_2968_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_op_2969_ = leanh::lean_ctor_get_uint8(
                                        v_l_2944_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    v_rhs_2970_ = leanh::lean_ctor_get(v_l_2944_, 2);
                                    v_lhs_2971_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v_op_2972_ = leanh::lean_ctor_get_uint8(
                                        v_r_2945_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    v_rhs_2973_ = leanh::lean_ctor_get(v_r_2945_, 2);
                                    v___x_2974_ = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(
                                        v_op_2969_, v_op_2972_,
                                    );
                                    if v___x_2974_ == 0 {
                                        return v___x_2974_;
                                    } else {
                                        v___x_2975_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(
                                            v_lhs_2968_,
                                            v_lhs_2971_,
                                        );
                                        if v___x_2975_ == 0 {
                                            return v___x_2975_;
                                        } else {
                                            v_l_2944_ = v_rhs_2970_;
                                            v_r_2945_ = v_rhs_2973_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            4 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 4 {
                                    v_op_2977_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_operand_2978_ = leanh::lean_ctor_get(v_l_2944_, 2);
                                    v_op_2979_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v_operand_2980_ = leanh::lean_ctor_get(v_r_2945_, 2);
                                    v___x_2981_ = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp_decEq(
                                        v_op_2977_, v_op_2979_,
                                    );
                                    if v___x_2981_ == 0 {
                                        return v___x_2981_;
                                    } else {
                                        v_l_2944_ = v_operand_2978_;
                                        v_r_2945_ = v_operand_2980_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            5 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 5 {
                                    v_l_2983_ = leanh::lean_ctor_get(v_l_2944_, 0);
                                    v_r_2984_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_lhs_2985_ = leanh::lean_ctor_get(v_l_2944_, 3);
                                    v_rhs_2986_ = leanh::lean_ctor_get(v_l_2944_, 4);
                                    v_l_2987_ = leanh::lean_ctor_get(v_r_2945_, 0);
                                    v_r_2988_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v_lhs_2989_ = leanh::lean_ctor_get(v_r_2945_, 3);
                                    v_rhs_2990_ = leanh::lean_ctor_get(v_r_2945_, 4);
                                    v___x_2991_ = lean_nat_dec_eq(v_l_2983_, v_l_2987_);
                                    if v___x_2991_ == 0 {
                                        return v___x_2991_;
                                    } else {
                                        v___x_2992_ = lean_nat_dec_eq(v_r_2984_, v_r_2988_);
                                        if v___x_2992_ == 0 {
                                            return v___x_2992_;
                                        } else {
                                            v___x_2993_ =
                                                l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(
                                                    v_lhs_2985_,
                                                    v_lhs_2989_,
                                                );
                                            if v___x_2993_ == 0 {
                                                return v___x_2993_;
                                            } else {
                                                v_l_2944_ = v_rhs_2986_;
                                                v_r_2945_ = v_rhs_2990_;
                                                state = 0;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            6 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 6 {
                                    v_w_2995_ = leanh::lean_ctor_get(v_l_2944_, 0);
                                    v_n_2996_ = leanh::lean_ctor_get(v_l_2944_, 2);
                                    v_expr_2997_ = leanh::lean_ctor_get(v_l_2944_, 3);
                                    v_w_2998_ = leanh::lean_ctor_get(v_r_2945_, 0);
                                    v_n_2999_ = leanh::lean_ctor_get(v_r_2945_, 2);
                                    v_expr_3000_ = leanh::lean_ctor_get(v_r_2945_, 3);
                                    v___x_3001_ = lean_nat_dec_eq(v_n_2996_, v_n_2999_);
                                    if v___x_3001_ == 0 {
                                        return v___x_3001_;
                                    } else {
                                        v___x_3002_ = lean_nat_dec_eq(v_w_2995_, v_w_2998_);
                                        if v___x_3002_ == 0 {
                                            return v___x_3002_;
                                        } else {
                                            v_l_2944_ = v_expr_2997_;
                                            v_r_2945_ = v_expr_3000_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            7 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 7 {
                                    v_n_3004_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_lhs_3005_ = leanh::lean_ctor_get(v_l_2944_, 2);
                                    v_rhs_3006_ = leanh::lean_ctor_get(v_l_2944_, 3);
                                    v_n_3007_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v_lhs_3008_ = leanh::lean_ctor_get(v_r_2945_, 2);
                                    v_rhs_3009_ = leanh::lean_ctor_get(v_r_2945_, 3);
                                    v___x_3010_ = lean_nat_dec_eq(v_n_3004_, v_n_3007_);
                                    if v___x_3010_ == 0 {
                                        return v___x_3010_;
                                    } else {
                                        v___x_3011_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(
                                            v_lhs_3005_,
                                            v_lhs_3008_,
                                        );
                                        if v___x_3011_ == 0 {
                                            return v___x_3011_;
                                        } else {
                                            v_l_2944_ = v_rhs_3006_;
                                            v_r_2945_ = v_rhs_3009_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            8 => {
                                if leanh::lean_obj_tag(v_r_2945_) == 8 {
                                    v_n_3013_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_lhs_3014_ = leanh::lean_ctor_get(v_l_2944_, 2);
                                    v_rhs_3015_ = leanh::lean_ctor_get(v_l_2944_, 3);
                                    v_n_3016_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v_lhs_3017_ = leanh::lean_ctor_get(v_r_2945_, 2);
                                    v_rhs_3018_ = leanh::lean_ctor_get(v_r_2945_, 3);
                                    v___x_3019_ = lean_nat_dec_eq(v_n_3013_, v_n_3016_);
                                    if v___x_3019_ == 0 {
                                        return v___x_3019_;
                                    } else {
                                        v___x_3020_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(
                                            v_lhs_3014_,
                                            v_lhs_3017_,
                                        );
                                        if v___x_3020_ == 0 {
                                            return v___x_3020_;
                                        } else {
                                            v_l_2944_ = v_rhs_3015_;
                                            v_r_2945_ = v_rhs_3018_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                            _ => {
                                if leanh::lean_obj_tag(v_r_2945_) == 9 {
                                    v_n_3022_ = leanh::lean_ctor_get(v_l_2944_, 1);
                                    v_lhs_3023_ = leanh::lean_ctor_get(v_l_2944_, 2);
                                    v_rhs_3024_ = leanh::lean_ctor_get(v_l_2944_, 3);
                                    v_n_3025_ = leanh::lean_ctor_get(v_r_2945_, 1);
                                    v_lhs_3026_ = leanh::lean_ctor_get(v_r_2945_, 2);
                                    v_rhs_3027_ = leanh::lean_ctor_get(v_r_2945_, 3);
                                    v___x_3028_ = lean_nat_dec_eq(v_n_3022_, v_n_3025_);
                                    if v___x_3028_ == 0 {
                                        return v___x_3028_;
                                    } else {
                                        v___x_3029_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(
                                            v_lhs_3023_,
                                            v_lhs_3026_,
                                        );
                                        if v___x_3029_ == 0 {
                                            return v___x_3029_;
                                        } else {
                                            v_l_2944_ = v_rhs_3024_;
                                            v_r_2945_ = v_rhs_3027_;
                                            state = 0;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v___x_2948_;
                                }
                            }
                        }
                    } else {
                        return v___x_2948_;
                    }
                }
            }
            2 => match leanh::lean_obj_tag(v_r_2945_) {
                0 => {
                    v_hashCode_3033_ = leanh::lean_ctor_get_uint64(
                        v_r_2945_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2950_ = v___y_3032_;
                    v___y_2951_ = v_hashCode_3033_;
                    state = 1;
                    continue;
                }
                1 => {
                    v_hashCode_3034_ = leanh::lean_ctor_get_uint64(
                        v_r_2945_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2950_ = v___y_3032_;
                    v___y_2951_ = v_hashCode_3034_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_hashCode_3035_ = leanh::lean_ctor_get_uint64(
                        v_r_2945_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2950_ = v___y_3032_;
                    v___y_2951_ = v_hashCode_3035_;
                    state = 1;
                    continue;
                }
                4 => {
                    v_hashCode_3036_ = leanh::lean_ctor_get_uint64(
                        v_r_2945_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v___y_2950_ = v___y_3032_;
                    v___y_2951_ = v_hashCode_3036_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_hashCode_3037_ = leanh::lean_ctor_get_uint64(
                        v_r_2945_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    v___y_2950_ = v___y_3032_;
                    v___y_2951_ = v_hashCode_3037_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_hashCode_3038_ = leanh::lean_ctor_get_uint64(
                        v_r_2945_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    );
                    v___y_2950_ = v___y_3032_;
                    v___y_2951_ = v_hashCode_3038_;
                    state = 1;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(
    mut v_l_3045_: *mut leanh::LeanObject,
    mut v_r_3046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3047_: u8 = 0;
    let mut v_r_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3047_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_3045_, v_r_3046_);
    leanh::lean_dec_ref(v_r_3046_);
    leanh::lean_dec_ref(v_l_3045_);
    v_r_3048_ = leanh::lean_box((v_res_3047_) as usize);
    return v_r_3048_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_decEq(
    mut v_w_3049_: *mut leanh::LeanObject,
    mut v_l_3050_: *mut leanh::LeanObject,
    mut v_r_3051_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3052_: u8 = 0;
    v___x_3052_ = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(v_l_3050_, v_r_3051_);
    return v___x_3052_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(
    mut v_w_3053_: *mut leanh::LeanObject,
    mut v_l_3054_: *mut leanh::LeanObject,
    mut v_r_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3056_: u8 = 0;
    let mut v_r_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3056_ = l_Std_Tactic_BVDecide_BVExpr_decEq(v_w_3053_, v_l_3054_, v_r_3055_);
    leanh::lean_dec_ref(v_r_3055_);
    leanh::lean_dec_ref(v_l_3054_);
    leanh::lean_dec(v_w_3053_);
    v_r_3057_ = leanh::lean_box((v_res_3056_) as usize);
    return v_r_3057_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_toString(
    mut v_w_3067_: *mut leanh::LeanObject,
    mut v_x_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3068_) {
        0 => {
            let mut v_idx_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_w_3067_);
            v_idx_3069_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_idx_3069_);
            leanh::lean_dec_ref_known(v_x_3068_, 2);
            v___x_3070_ = l_Std_Tactic_BVDecide_instReprBVBit_repr___redArg___closed__1;
            v___x_3071_ = l_Nat_reprFast(v_idx_3069_);
            v___x_3072_ = lean_string_append(v___x_3070_, v___x_3071_);
            leanh::lean_dec_ref(v___x_3071_);
            return v___x_3072_;
        }
        1 => {
            let mut v_val_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_3073_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_val_3073_);
            leanh::lean_dec_ref_known(v_x_3068_, 2);
            v___x_3074_ = l_BitVec_repr(v_w_3067_, v_val_3073_);
            v___x_3075_ = l_Std_Format_defWidth;
            v___x_3076_ = leanh::lean_unsigned_to_nat(0);
            v___x_3077_ = l_Std_Format_pretty(v___x_3074_, v___x_3075_, v___x_3076_, v___x_3076_);
            return v___x_3077_;
        }
        2 => {
            let mut v_w_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_3078_ = leanh::lean_ctor_get(v_x_3068_, 0);
            leanh::lean_inc(v_w_3078_);
            v_start_3079_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_start_3079_);
            v_expr_3080_ = leanh::lean_ctor_get(v_x_3068_, 3);
            leanh::lean_inc_ref(v_expr_3080_);
            leanh::lean_dec_ref_known(v_x_3068_, 4);
            v___x_3081_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3078_, v_expr_3080_);
            v___x_3082_ = l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1;
            v___x_3083_ = lean_string_append(v___x_3081_, v___x_3082_);
            v___x_3084_ = l_Nat_reprFast(v_start_3079_);
            v___x_3085_ = lean_string_append(v___x_3083_, v___x_3084_);
            leanh::lean_dec_ref(v___x_3084_);
            v___x_3086_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__0;
            v___x_3087_ = lean_string_append(v___x_3085_, v___x_3086_);
            v___x_3088_ = l_Nat_reprFast(v_w_3067_);
            v___x_3089_ = lean_string_append(v___x_3087_, v___x_3088_);
            leanh::lean_dec_ref(v___x_3088_);
            v___x_3090_ = l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2;
            v___x_3091_ = lean_string_append(v___x_3089_, v___x_3090_);
            return v___x_3091_;
        }
        3 => {
            let mut v_lhs_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_3093_: u8 = 0;
            let mut v_rhs_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_3092_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc_ref(v_lhs_3092_);
            v_op_3093_ = leanh::lean_ctor_get_uint8(
                v_x_3068_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_3094_ = leanh::lean_ctor_get(v_x_3068_, 2);
            leanh::lean_inc_ref(v_rhs_3094_);
            leanh::lean_dec_ref_known(v_x_3068_, 3);
            v___x_3095_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
            leanh::lean_inc(v_w_3067_);
            v___x_3096_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3067_, v_lhs_3092_);
            v___x_3097_ = lean_string_append(v___x_3095_, v___x_3096_);
            leanh::lean_dec_ref(v___x_3096_);
            v___x_3098_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__2;
            v___x_3099_ = lean_string_append(v___x_3097_, v___x_3098_);
            v___x_3100_ = l_Std_Tactic_BVDecide_BVBinOp_toString(v_op_3093_);
            v___x_3101_ = lean_string_append(v___x_3099_, v___x_3100_);
            leanh::lean_dec_ref(v___x_3100_);
            v___x_3102_ = lean_string_append(v___x_3101_, v___x_3098_);
            v___x_3103_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3067_, v_rhs_3094_);
            v___x_3104_ = lean_string_append(v___x_3102_, v___x_3103_);
            leanh::lean_dec_ref(v___x_3103_);
            v___x_3105_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
            v___x_3106_ = lean_string_append(v___x_3104_, v___x_3105_);
            return v___x_3106_;
        }
        4 => {
            let mut v_op_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_op_3107_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_op_3107_);
            v_operand_3108_ = leanh::lean_ctor_get(v_x_3068_, 2);
            leanh::lean_inc_ref(v_operand_3108_);
            leanh::lean_dec_ref_known(v_x_3068_, 3);
            v___x_3109_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
            v___x_3110_ = l_Std_Tactic_BVDecide_BVUnOp_toString(v_op_3107_);
            v___x_3111_ = lean_string_append(v___x_3109_, v___x_3110_);
            leanh::lean_dec_ref(v___x_3110_);
            v___x_3112_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__2;
            v___x_3113_ = lean_string_append(v___x_3111_, v___x_3112_);
            v___x_3114_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3067_, v_operand_3108_);
            v___x_3115_ = lean_string_append(v___x_3113_, v___x_3114_);
            leanh::lean_dec_ref(v___x_3114_);
            v___x_3116_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
            v___x_3117_ = lean_string_append(v___x_3115_, v___x_3116_);
            return v___x_3117_;
        }
        5 => {
            let mut v_l_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_w_3067_);
            v_l_3118_ = leanh::lean_ctor_get(v_x_3068_, 0);
            leanh::lean_inc(v_l_3118_);
            v_r_3119_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_r_3119_);
            v_lhs_3120_ = leanh::lean_ctor_get(v_x_3068_, 3);
            leanh::lean_inc_ref(v_lhs_3120_);
            v_rhs_3121_ = leanh::lean_ctor_get(v_x_3068_, 4);
            leanh::lean_inc_ref(v_rhs_3121_);
            leanh::lean_dec_ref_known(v_x_3068_, 5);
            v___x_3122_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
            v___x_3123_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_l_3118_, v_lhs_3120_);
            v___x_3124_ = lean_string_append(v___x_3122_, v___x_3123_);
            leanh::lean_dec_ref(v___x_3123_);
            v___x_3125_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__4;
            v___x_3126_ = lean_string_append(v___x_3124_, v___x_3125_);
            v___x_3127_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_r_3119_, v_rhs_3121_);
            v___x_3128_ = lean_string_append(v___x_3126_, v___x_3127_);
            leanh::lean_dec_ref(v___x_3127_);
            v___x_3129_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
            v___x_3130_ = lean_string_append(v___x_3128_, v___x_3129_);
            return v___x_3130_;
        }
        6 => {
            let mut v_w_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_w_3067_);
            v_w_3131_ = leanh::lean_ctor_get(v_x_3068_, 0);
            leanh::lean_inc(v_w_3131_);
            v_n_3132_ = leanh::lean_ctor_get(v_x_3068_, 2);
            leanh::lean_inc(v_n_3132_);
            v_expr_3133_ = leanh::lean_ctor_get(v_x_3068_, 3);
            leanh::lean_inc_ref(v_expr_3133_);
            leanh::lean_dec_ref_known(v_x_3068_, 4);
            v___x_3134_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__5;
            v___x_3135_ = l_Nat_reprFast(v_n_3132_);
            v___x_3136_ = lean_string_append(v___x_3134_, v___x_3135_);
            leanh::lean_dec_ref(v___x_3135_);
            v___x_3137_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__2;
            v___x_3138_ = lean_string_append(v___x_3136_, v___x_3137_);
            v___x_3139_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3131_, v_expr_3133_);
            v___x_3140_ = lean_string_append(v___x_3138_, v___x_3139_);
            leanh::lean_dec_ref(v___x_3139_);
            v___x_3141_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
            v___x_3142_ = lean_string_append(v___x_3140_, v___x_3141_);
            return v___x_3142_;
        }
        7 => {
            let mut v_n_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_3143_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_n_3143_);
            v_lhs_3144_ = leanh::lean_ctor_get(v_x_3068_, 2);
            leanh::lean_inc_ref(v_lhs_3144_);
            v_rhs_3145_ = leanh::lean_ctor_get(v_x_3068_, 3);
            leanh::lean_inc_ref(v_rhs_3145_);
            leanh::lean_dec_ref_known(v_x_3068_, 4);
            v___x_3146_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
            v___x_3147_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3067_, v_lhs_3144_);
            v___x_3148_ = lean_string_append(v___x_3146_, v___x_3147_);
            leanh::lean_dec_ref(v___x_3147_);
            v___x_3149_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__6;
            v___x_3150_ = lean_string_append(v___x_3148_, v___x_3149_);
            v___x_3151_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_3143_, v_rhs_3145_);
            v___x_3152_ = lean_string_append(v___x_3150_, v___x_3151_);
            leanh::lean_dec_ref(v___x_3151_);
            v___x_3153_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
            v___x_3154_ = lean_string_append(v___x_3152_, v___x_3153_);
            return v___x_3154_;
        }
        8 => {
            let mut v_n_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_3155_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_n_3155_);
            v_lhs_3156_ = leanh::lean_ctor_get(v_x_3068_, 2);
            leanh::lean_inc_ref(v_lhs_3156_);
            v_rhs_3157_ = leanh::lean_ctor_get(v_x_3068_, 3);
            leanh::lean_inc_ref(v_rhs_3157_);
            leanh::lean_dec_ref_known(v_x_3068_, 4);
            v___x_3158_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
            v___x_3159_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3067_, v_lhs_3156_);
            v___x_3160_ = lean_string_append(v___x_3158_, v___x_3159_);
            leanh::lean_dec_ref(v___x_3159_);
            v___x_3161_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__7;
            v___x_3162_ = lean_string_append(v___x_3160_, v___x_3161_);
            v___x_3163_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_3155_, v_rhs_3157_);
            v___x_3164_ = lean_string_append(v___x_3162_, v___x_3163_);
            leanh::lean_dec_ref(v___x_3163_);
            v___x_3165_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
            v___x_3166_ = lean_string_append(v___x_3164_, v___x_3165_);
            return v___x_3166_;
        }
        _ => {
            let mut v_n_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_3167_ = leanh::lean_ctor_get(v_x_3068_, 1);
            leanh::lean_inc(v_n_3167_);
            v_lhs_3168_ = leanh::lean_ctor_get(v_x_3068_, 2);
            leanh::lean_inc_ref(v_lhs_3168_);
            v_rhs_3169_ = leanh::lean_ctor_get(v_x_3068_, 3);
            leanh::lean_inc_ref(v_rhs_3169_);
            leanh::lean_dec_ref_known(v_x_3068_, 4);
            v___x_3170_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
            v___x_3171_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3067_, v_lhs_3168_);
            v___x_3172_ = lean_string_append(v___x_3170_, v___x_3171_);
            leanh::lean_dec_ref(v___x_3171_);
            v___x_3173_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__8;
            v___x_3174_ = lean_string_append(v___x_3172_, v___x_3173_);
            v___x_3175_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_n_3167_, v_rhs_3169_);
            v___x_3176_ = lean_string_append(v___x_3174_, v___x_3175_);
            leanh::lean_dec_ref(v___x_3175_);
            v___x_3177_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
            v___x_3178_ = lean_string_append(v___x_3176_, v___x_3177_);
            return v___x_3178_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_instToString(
    mut v_w_3179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3180_ = leanh::lean_alloc_closure(
        l_Std_Tactic_BVDecide_BVExpr_toString as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_3180_, 0, v_w_3179_);
    return v___x_3180_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Assignment_get(
    mut v_assign_3181_: *mut leanh::LeanObject,
    mut v_idx_3182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3183_ = l_Lean_RArray_getImpl___redArg(v_assign_3181_, v_idx_3182_);
    return v___x_3183_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(
    mut v_assign_3184_: *mut leanh::LeanObject,
    mut v_idx_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3186_ = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(v_assign_3184_, v_idx_3185_);
    leanh::lean_dec(v_idx_3185_);
    leanh::lean_dec_ref(v_assign_3184_);
    return v_res_3186_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_eval(
    mut v_w_3187_: *mut leanh::LeanObject,
    mut v_assign_3188_: *mut leanh::LeanObject,
    mut v_x_3189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3189_) {
        0 => {
            let mut v_idx_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_packedBv_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_w_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_bv_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3194_: u8 = 0;
            v_idx_3190_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc(v_idx_3190_);
            leanh::lean_dec_ref_known(v_x_3189_, 2);
            v_packedBv_3191_ = l_Lean_RArray_getImpl___redArg(v_assign_3188_, v_idx_3190_);
            leanh::lean_dec(v_idx_3190_);
            v_w_3192_ = leanh::lean_ctor_get(v_packedBv_3191_, 0);
            leanh::lean_inc(v_w_3192_);
            v_bv_3193_ = leanh::lean_ctor_get(v_packedBv_3191_, 1);
            leanh::lean_inc(v_bv_3193_);
            leanh::lean_dec(v_packedBv_3191_);
            v___x_3194_ = lean_nat_dec_eq(v_w_3192_, v_w_3187_);
            if v___x_3194_ == 0 {
                let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3195_ = l_BitVec_setWidth(v_w_3192_, v_w_3187_, v_bv_3193_);
                leanh::lean_dec(v_bv_3193_);
                leanh::lean_dec(v_w_3187_);
                leanh::lean_dec(v_w_3192_);
                return v___x_3195_;
            } else {
                leanh::lean_dec(v_w_3192_);
                leanh::lean_dec(v_w_3187_);
                return v_bv_3193_;
            }
        }
        1 => {
            let mut v_val_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_w_3187_);
            v_val_3196_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc(v_val_3196_);
            leanh::lean_dec_ref_known(v_x_3189_, 2);
            return v_val_3196_;
        }
        2 => {
            let mut v_w_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_w_3197_ = leanh::lean_ctor_get(v_x_3189_, 0);
            leanh::lean_inc(v_w_3197_);
            v_start_3198_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc(v_start_3198_);
            v_expr_3199_ = leanh::lean_ctor_get(v_x_3189_, 3);
            leanh::lean_inc_ref(v_expr_3199_);
            leanh::lean_dec_ref_known(v_x_3189_, 4);
            v___x_3200_ =
                l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3197_, v_assign_3188_, v_expr_3199_);
            v___x_3201_ = l_BitVec_extractLsb_x27___redArg(v_start_3198_, v_w_3187_, v___x_3200_);
            leanh::lean_dec(v___x_3200_);
            leanh::lean_dec(v_w_3187_);
            leanh::lean_dec(v_start_3198_);
            return v___x_3201_;
        }
        3 => {
            let mut v_lhs_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_3203_: u8 = 0;
            let mut v_rhs_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_lhs_3202_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc_ref(v_lhs_3202_);
            v_op_3203_ = leanh::lean_ctor_get_uint8(
                v_x_3189_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_3204_ = leanh::lean_ctor_get(v_x_3189_, 2);
            leanh::lean_inc_ref(v_rhs_3204_);
            leanh::lean_dec_ref_known(v_x_3189_, 3);
            leanh::lean_inc_n(v_w_3187_, 2);
            v___x_3205_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3187_, v_assign_3188_, v_lhs_3202_);
            v___x_3206_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3187_, v_assign_3188_, v_rhs_3204_);
            v___x_3207_ =
                l_Std_Tactic_BVDecide_BVBinOp_eval(v_w_3187_, v_op_3203_, v___x_3205_, v___x_3206_);
            leanh::lean_dec(v___x_3206_);
            leanh::lean_dec(v___x_3205_);
            leanh::lean_dec(v_w_3187_);
            return v___x_3207_;
        }
        4 => {
            let mut v_op_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_op_3208_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc(v_op_3208_);
            v_operand_3209_ = leanh::lean_ctor_get(v_x_3189_, 2);
            leanh::lean_inc_ref(v_operand_3209_);
            leanh::lean_dec_ref_known(v_x_3189_, 3);
            leanh::lean_inc(v_w_3187_);
            v___x_3210_ =
                l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3187_, v_assign_3188_, v_operand_3209_);
            v___x_3211_ = l_Std_Tactic_BVDecide_BVUnOp_eval(v_w_3187_, v_op_3208_, v___x_3210_);
            leanh::lean_dec(v_op_3208_);
            return v___x_3211_;
        }
        5 => {
            let mut v_l_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_w_3187_);
            v_l_3212_ = leanh::lean_ctor_get(v_x_3189_, 0);
            leanh::lean_inc(v_l_3212_);
            v_r_3213_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc_n(v_r_3213_, 2);
            v_lhs_3214_ = leanh::lean_ctor_get(v_x_3189_, 3);
            leanh::lean_inc_ref(v_lhs_3214_);
            v_rhs_3215_ = leanh::lean_ctor_get(v_x_3189_, 4);
            leanh::lean_inc_ref(v_rhs_3215_);
            leanh::lean_dec_ref_known(v_x_3189_, 5);
            v___x_3216_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_l_3212_, v_assign_3188_, v_lhs_3214_);
            v___x_3217_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_r_3213_, v_assign_3188_, v_rhs_3215_);
            v___x_3218_ = l_BitVec_append___redArg(v_r_3213_, v___x_3216_, v___x_3217_);
            leanh::lean_dec(v___x_3217_);
            leanh::lean_dec(v___x_3216_);
            leanh::lean_dec(v_r_3213_);
            return v___x_3218_;
        }
        6 => {
            let mut v_w_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_w_3187_);
            v_w_3219_ = leanh::lean_ctor_get(v_x_3189_, 0);
            leanh::lean_inc_n(v_w_3219_, 2);
            v_n_3220_ = leanh::lean_ctor_get(v_x_3189_, 2);
            leanh::lean_inc(v_n_3220_);
            v_expr_3221_ = leanh::lean_ctor_get(v_x_3189_, 3);
            leanh::lean_inc_ref(v_expr_3221_);
            leanh::lean_dec_ref_known(v_x_3189_, 4);
            v___x_3222_ =
                l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3219_, v_assign_3188_, v_expr_3221_);
            v___x_3223_ = l_BitVec_replicate(v_w_3219_, v_n_3220_, v___x_3222_);
            leanh::lean_dec(v___x_3222_);
            leanh::lean_dec(v_n_3220_);
            leanh::lean_dec(v_w_3219_);
            return v___x_3223_;
        }
        7 => {
            let mut v_n_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_3224_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc(v_n_3224_);
            v_lhs_3225_ = leanh::lean_ctor_get(v_x_3189_, 2);
            leanh::lean_inc_ref(v_lhs_3225_);
            v_rhs_3226_ = leanh::lean_ctor_get(v_x_3189_, 3);
            leanh::lean_inc_ref(v_rhs_3226_);
            leanh::lean_dec_ref_known(v_x_3189_, 4);
            leanh::lean_inc(v_w_3187_);
            v___x_3227_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3187_, v_assign_3188_, v_lhs_3225_);
            v___x_3228_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_3224_, v_assign_3188_, v_rhs_3226_);
            v___x_3229_ = l_BitVec_shiftLeft(v_w_3187_, v___x_3227_, v___x_3228_);
            leanh::lean_dec(v___x_3228_);
            leanh::lean_dec(v___x_3227_);
            leanh::lean_dec(v_w_3187_);
            return v___x_3229_;
        }
        8 => {
            let mut v_n_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_3230_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc(v_n_3230_);
            v_lhs_3231_ = leanh::lean_ctor_get(v_x_3189_, 2);
            leanh::lean_inc_ref(v_lhs_3231_);
            v_rhs_3232_ = leanh::lean_ctor_get(v_x_3189_, 3);
            leanh::lean_inc_ref(v_rhs_3232_);
            leanh::lean_dec_ref_known(v_x_3189_, 4);
            v___x_3233_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3187_, v_assign_3188_, v_lhs_3231_);
            v___x_3234_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_3230_, v_assign_3188_, v_rhs_3232_);
            v___x_3235_ = lean_nat_shiftr(v___x_3233_, v___x_3234_);
            leanh::lean_dec(v___x_3234_);
            leanh::lean_dec(v___x_3233_);
            return v___x_3235_;
        }
        _ => {
            let mut v_n_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_n_3236_ = leanh::lean_ctor_get(v_x_3189_, 1);
            leanh::lean_inc(v_n_3236_);
            v_lhs_3237_ = leanh::lean_ctor_get(v_x_3189_, 2);
            leanh::lean_inc_ref(v_lhs_3237_);
            v_rhs_3238_ = leanh::lean_ctor_get(v_x_3189_, 3);
            leanh::lean_inc_ref(v_rhs_3238_);
            leanh::lean_dec_ref_known(v_x_3189_, 4);
            leanh::lean_inc(v_w_3187_);
            v___x_3239_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3187_, v_assign_3188_, v_lhs_3237_);
            v___x_3240_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_n_3236_, v_assign_3188_, v_rhs_3238_);
            v___x_3241_ = l_BitVec_sshiftRight(v_w_3187_, v___x_3239_, v___x_3240_);
            leanh::lean_dec(v___x_3240_);
            leanh::lean_dec(v_w_3187_);
            return v___x_3241_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_eval___boxed(
    mut v_w_3242_: *mut leanh::LeanObject,
    mut v_assign_3243_: *mut leanh::LeanObject,
    mut v_x_3244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3245_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3242_, v_assign_3243_, v_x_3244_);
    leanh::lean_dec_ref(v_assign_3243_);
    return v_res_3245_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(
    mut v_w_3246_: *mut leanh::LeanObject,
    mut v_x_3247_: *mut leanh::LeanObject,
    mut v_h__1_3248_: *mut leanh::LeanObject,
    mut v_h__2_3249_: *mut leanh::LeanObject,
    mut v_h__3_3250_: *mut leanh::LeanObject,
    mut v_h__4_3251_: *mut leanh::LeanObject,
    mut v_h__5_3252_: *mut leanh::LeanObject,
    mut v_h__6_3253_: *mut leanh::LeanObject,
    mut v_h__7_3254_: *mut leanh::LeanObject,
    mut v_h__8_3255_: *mut leanh::LeanObject,
    mut v_h__9_3256_: *mut leanh::LeanObject,
    mut v_h__10_3257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3247_) {
        0 => {
            let mut v_idx_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            v_idx_3258_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_idx_3258_);
            leanh::lean_dec_ref_known(v_x_3247_, 2);
            v___x_3259_ = leanh::lean_apply_2(v_h__1_3248_, v_w_3246_, v_idx_3258_);
            return v___x_3259_;
        }
        1 => {
            let mut v_val_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__1_3248_);
            v_val_3260_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_val_3260_);
            leanh::lean_dec_ref_known(v_x_3247_, 2);
            v___x_3261_ = leanh::lean_apply_2(v_h__2_3249_, v_w_3246_, v_val_3260_);
            return v___x_3261_;
        }
        2 => {
            let mut v_w_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_w_3262_ = leanh::lean_ctor_get(v_x_3247_, 0);
            leanh::lean_inc(v_w_3262_);
            v_start_3263_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_start_3263_);
            v_expr_3264_ = leanh::lean_ctor_get(v_x_3247_, 3);
            leanh::lean_inc_ref(v_expr_3264_);
            leanh::lean_dec_ref_known(v_x_3247_, 4);
            v___x_3265_ = leanh::lean_apply_4(
                v_h__3_3250_,
                v_w_3246_,
                v_w_3262_,
                v_start_3263_,
                v_expr_3264_,
            );
            return v___x_3265_;
        }
        3 => {
            let mut v_lhs_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_3267_: u8 = 0;
            let mut v_rhs_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_lhs_3266_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc_ref(v_lhs_3266_);
            v_op_3267_ = leanh::lean_ctor_get_uint8(
                v_x_3247_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_3268_ = leanh::lean_ctor_get(v_x_3247_, 2);
            leanh::lean_inc_ref(v_rhs_3268_);
            leanh::lean_dec_ref_known(v_x_3247_, 3);
            v___x_3269_ = leanh::lean_box((v_op_3267_) as usize);
            v___x_3270_ = leanh::lean_apply_4(
                v_h__4_3251_,
                v_w_3246_,
                v_lhs_3266_,
                v___x_3269_,
                v_rhs_3268_,
            );
            return v___x_3270_;
        }
        4 => {
            let mut v_op_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_op_3271_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_op_3271_);
            v_operand_3272_ = leanh::lean_ctor_get(v_x_3247_, 2);
            leanh::lean_inc_ref(v_operand_3272_);
            leanh::lean_dec_ref_known(v_x_3247_, 3);
            v___x_3273_ =
                leanh::lean_apply_3(v_h__5_3252_, v_w_3246_, v_op_3271_, v_operand_3272_);
            return v___x_3273_;
        }
        5 => {
            let mut v_l_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_l_3274_ = leanh::lean_ctor_get(v_x_3247_, 0);
            leanh::lean_inc(v_l_3274_);
            v_r_3275_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_r_3275_);
            v_lhs_3276_ = leanh::lean_ctor_get(v_x_3247_, 3);
            leanh::lean_inc_ref(v_lhs_3276_);
            v_rhs_3277_ = leanh::lean_ctor_get(v_x_3247_, 4);
            leanh::lean_inc_ref(v_rhs_3277_);
            leanh::lean_dec_ref_known(v_x_3247_, 5);
            v___x_3278_ = leanh::lean_apply_6(
                v_h__6_3253_,
                v_w_3246_,
                v_l_3274_,
                v_r_3275_,
                v_lhs_3276_,
                v_rhs_3277_,
                leanh::lean_box(0),
            );
            return v___x_3278_;
        }
        6 => {
            let mut v_w_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_w_3279_ = leanh::lean_ctor_get(v_x_3247_, 0);
            leanh::lean_inc(v_w_3279_);
            v_n_3280_ = leanh::lean_ctor_get(v_x_3247_, 2);
            leanh::lean_inc(v_n_3280_);
            v_expr_3281_ = leanh::lean_ctor_get(v_x_3247_, 3);
            leanh::lean_inc_ref(v_expr_3281_);
            leanh::lean_dec_ref_known(v_x_3247_, 4);
            v___x_3282_ = leanh::lean_apply_5(
                v_h__7_3254_,
                v_w_3246_,
                v_w_3279_,
                v_n_3280_,
                v_expr_3281_,
                leanh::lean_box(0),
            );
            return v___x_3282_;
        }
        7 => {
            let mut v_n_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_n_3283_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_n_3283_);
            v_lhs_3284_ = leanh::lean_ctor_get(v_x_3247_, 2);
            leanh::lean_inc_ref(v_lhs_3284_);
            v_rhs_3285_ = leanh::lean_ctor_get(v_x_3247_, 3);
            leanh::lean_inc_ref(v_rhs_3285_);
            leanh::lean_dec_ref_known(v_x_3247_, 4);
            v___x_3286_ = leanh::lean_apply_4(
                v_h__8_3255_,
                v_w_3246_,
                v_n_3283_,
                v_lhs_3284_,
                v_rhs_3285_,
            );
            return v___x_3286_;
        }
        8 => {
            let mut v_n_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3257_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_n_3287_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_n_3287_);
            v_lhs_3288_ = leanh::lean_ctor_get(v_x_3247_, 2);
            leanh::lean_inc_ref(v_lhs_3288_);
            v_rhs_3289_ = leanh::lean_ctor_get(v_x_3247_, 3);
            leanh::lean_inc_ref(v_rhs_3289_);
            leanh::lean_dec_ref_known(v_x_3247_, 4);
            v___x_3290_ = leanh::lean_apply_4(
                v_h__9_3256_,
                v_w_3246_,
                v_n_3287_,
                v_lhs_3288_,
                v_rhs_3289_,
            );
            return v___x_3290_;
        }
        _ => {
            let mut v_n_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_3256_);
            leanh::lean_dec(v_h__8_3255_);
            leanh::lean_dec(v_h__7_3254_);
            leanh::lean_dec(v_h__6_3253_);
            leanh::lean_dec(v_h__5_3252_);
            leanh::lean_dec(v_h__4_3251_);
            leanh::lean_dec(v_h__3_3250_);
            leanh::lean_dec(v_h__2_3249_);
            leanh::lean_dec(v_h__1_3248_);
            v_n_3291_ = leanh::lean_ctor_get(v_x_3247_, 1);
            leanh::lean_inc(v_n_3291_);
            v_lhs_3292_ = leanh::lean_ctor_get(v_x_3247_, 2);
            leanh::lean_inc_ref(v_lhs_3292_);
            v_rhs_3293_ = leanh::lean_ctor_get(v_x_3247_, 3);
            leanh::lean_inc_ref(v_rhs_3293_);
            leanh::lean_dec_ref_known(v_x_3247_, 4);
            v___x_3294_ = leanh::lean_apply_4(
                v_h__10_3257_,
                v_w_3246_,
                v_n_3291_,
                v_lhs_3292_,
                v_rhs_3293_,
            );
            return v___x_3294_;
        }
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(
    mut v_motive_3295_: *mut leanh::LeanObject,
    mut v_w_3296_: *mut leanh::LeanObject,
    mut v_x_3297_: *mut leanh::LeanObject,
    mut v_h__1_3298_: *mut leanh::LeanObject,
    mut v_h__2_3299_: *mut leanh::LeanObject,
    mut v_h__3_3300_: *mut leanh::LeanObject,
    mut v_h__4_3301_: *mut leanh::LeanObject,
    mut v_h__5_3302_: *mut leanh::LeanObject,
    mut v_h__6_3303_: *mut leanh::LeanObject,
    mut v_h__7_3304_: *mut leanh::LeanObject,
    mut v_h__8_3305_: *mut leanh::LeanObject,
    mut v_h__9_3306_: *mut leanh::LeanObject,
    mut v_h__10_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3297_) {
        0 => {
            let mut v_idx_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            v_idx_3308_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_idx_3308_);
            leanh::lean_dec_ref_known(v_x_3297_, 2);
            v___x_3309_ = leanh::lean_apply_2(v_h__1_3298_, v_w_3296_, v_idx_3308_);
            return v___x_3309_;
        }
        1 => {
            let mut v_val_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__1_3298_);
            v_val_3310_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_val_3310_);
            leanh::lean_dec_ref_known(v_x_3297_, 2);
            v___x_3311_ = leanh::lean_apply_2(v_h__2_3299_, v_w_3296_, v_val_3310_);
            return v___x_3311_;
        }
        2 => {
            let mut v_w_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_w_3312_ = leanh::lean_ctor_get(v_x_3297_, 0);
            leanh::lean_inc(v_w_3312_);
            v_start_3313_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_start_3313_);
            v_expr_3314_ = leanh::lean_ctor_get(v_x_3297_, 3);
            leanh::lean_inc_ref(v_expr_3314_);
            leanh::lean_dec_ref_known(v_x_3297_, 4);
            v___x_3315_ = leanh::lean_apply_4(
                v_h__3_3300_,
                v_w_3296_,
                v_w_3312_,
                v_start_3313_,
                v_expr_3314_,
            );
            return v___x_3315_;
        }
        3 => {
            let mut v_lhs_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_op_3317_: u8 = 0;
            let mut v_rhs_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_lhs_3316_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc_ref(v_lhs_3316_);
            v_op_3317_ = leanh::lean_ctor_get_uint8(
                v_x_3297_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
            );
            v_rhs_3318_ = leanh::lean_ctor_get(v_x_3297_, 2);
            leanh::lean_inc_ref(v_rhs_3318_);
            leanh::lean_dec_ref_known(v_x_3297_, 3);
            v___x_3319_ = leanh::lean_box((v_op_3317_) as usize);
            v___x_3320_ = leanh::lean_apply_4(
                v_h__4_3301_,
                v_w_3296_,
                v_lhs_3316_,
                v___x_3319_,
                v_rhs_3318_,
            );
            return v___x_3320_;
        }
        4 => {
            let mut v_op_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_operand_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_op_3321_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_op_3321_);
            v_operand_3322_ = leanh::lean_ctor_get(v_x_3297_, 2);
            leanh::lean_inc_ref(v_operand_3322_);
            leanh::lean_dec_ref_known(v_x_3297_, 3);
            v___x_3323_ =
                leanh::lean_apply_3(v_h__5_3302_, v_w_3296_, v_op_3321_, v_operand_3322_);
            return v___x_3323_;
        }
        5 => {
            let mut v_l_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_l_3324_ = leanh::lean_ctor_get(v_x_3297_, 0);
            leanh::lean_inc(v_l_3324_);
            v_r_3325_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_r_3325_);
            v_lhs_3326_ = leanh::lean_ctor_get(v_x_3297_, 3);
            leanh::lean_inc_ref(v_lhs_3326_);
            v_rhs_3327_ = leanh::lean_ctor_get(v_x_3297_, 4);
            leanh::lean_inc_ref(v_rhs_3327_);
            leanh::lean_dec_ref_known(v_x_3297_, 5);
            v___x_3328_ = leanh::lean_apply_6(
                v_h__6_3303_,
                v_w_3296_,
                v_l_3324_,
                v_r_3325_,
                v_lhs_3326_,
                v_rhs_3327_,
                leanh::lean_box(0),
            );
            return v___x_3328_;
        }
        6 => {
            let mut v_w_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_w_3329_ = leanh::lean_ctor_get(v_x_3297_, 0);
            leanh::lean_inc(v_w_3329_);
            v_n_3330_ = leanh::lean_ctor_get(v_x_3297_, 2);
            leanh::lean_inc(v_n_3330_);
            v_expr_3331_ = leanh::lean_ctor_get(v_x_3297_, 3);
            leanh::lean_inc_ref(v_expr_3331_);
            leanh::lean_dec_ref_known(v_x_3297_, 4);
            v___x_3332_ = leanh::lean_apply_5(
                v_h__7_3304_,
                v_w_3296_,
                v_w_3329_,
                v_n_3330_,
                v_expr_3331_,
                leanh::lean_box(0),
            );
            return v___x_3332_;
        }
        7 => {
            let mut v_n_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_n_3333_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_n_3333_);
            v_lhs_3334_ = leanh::lean_ctor_get(v_x_3297_, 2);
            leanh::lean_inc_ref(v_lhs_3334_);
            v_rhs_3335_ = leanh::lean_ctor_get(v_x_3297_, 3);
            leanh::lean_inc_ref(v_rhs_3335_);
            leanh::lean_dec_ref_known(v_x_3297_, 4);
            v___x_3336_ = leanh::lean_apply_4(
                v_h__8_3305_,
                v_w_3296_,
                v_n_3333_,
                v_lhs_3334_,
                v_rhs_3335_,
            );
            return v___x_3336_;
        }
        8 => {
            let mut v_n_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__10_3307_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_n_3337_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_n_3337_);
            v_lhs_3338_ = leanh::lean_ctor_get(v_x_3297_, 2);
            leanh::lean_inc_ref(v_lhs_3338_);
            v_rhs_3339_ = leanh::lean_ctor_get(v_x_3297_, 3);
            leanh::lean_inc_ref(v_rhs_3339_);
            leanh::lean_dec_ref_known(v_x_3297_, 4);
            v___x_3340_ = leanh::lean_apply_4(
                v_h__9_3306_,
                v_w_3296_,
                v_n_3337_,
                v_lhs_3338_,
                v_rhs_3339_,
            );
            return v___x_3340_;
        }
        _ => {
            let mut v_n_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_lhs_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_rhs_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_3306_);
            leanh::lean_dec(v_h__8_3305_);
            leanh::lean_dec(v_h__7_3304_);
            leanh::lean_dec(v_h__6_3303_);
            leanh::lean_dec(v_h__5_3302_);
            leanh::lean_dec(v_h__4_3301_);
            leanh::lean_dec(v_h__3_3300_);
            leanh::lean_dec(v_h__2_3299_);
            leanh::lean_dec(v_h__1_3298_);
            v_n_3341_ = leanh::lean_ctor_get(v_x_3297_, 1);
            leanh::lean_inc(v_n_3341_);
            v_lhs_3342_ = leanh::lean_ctor_get(v_x_3297_, 2);
            leanh::lean_inc_ref(v_lhs_3342_);
            v_rhs_3343_ = leanh::lean_ctor_get(v_x_3297_, 3);
            leanh::lean_inc_ref(v_rhs_3343_);
            leanh::lean_dec_ref_known(v_x_3297_, 4);
            v___x_3344_ = leanh::lean_apply_4(
                v_h__10_3307_,
                v_w_3296_,
                v_n_3341_,
                v_lhs_3342_,
                v_rhs_3343_,
            );
            return v___x_3344_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(
    mut v_x_3345_: u8,
) -> *mut leanh::LeanObject {
    if v_x_3345_ == 0 {
        let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3346_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3346_;
    } else {
        let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3347_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3347_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ctorIdx___boxed(
    mut v_x_3348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_3349_: u8 = 0;
    let mut v_res_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_3349_ = (leanh::lean_unbox(v_x_3348_) as u8);
    v_res_3350_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(v_x_boxed_3349_);
    return v_res_3350_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(
    mut v_x_3351_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3352_ = l_Std_Tactic_BVDecide_BVBinPred_ctorIdx(v_x_3351_);
    return v___x_3352_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(
    mut v_x_3353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_3354_: u8 = 0;
    let mut v_res_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_3354_ = (leanh::lean_unbox(v_x_3353_) as u8);
    v_res_3355_ = l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(v_x_4__boxed_3354_);
    return v_res_3355_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(
    mut v_k_3356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_3356_);
    return v_k_3356_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg___boxed(
    mut v_k_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3358_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim___redArg(v_k_3357_);
    leanh::lean_dec(v_k_3357_);
    return v_res_3358_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ctorElim(
    mut v_motive_3359_: *mut leanh::LeanObject,
    mut v_ctorIdx_3360_: *mut leanh::LeanObject,
    mut v_t_3361_: u8,
    mut v_h_3362_: *mut leanh::LeanObject,
    mut v_k_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_3363_);
    return v_k_3363_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ctorElim___boxed(
    mut v_motive_3364_: *mut leanh::LeanObject,
    mut v_ctorIdx_3365_: *mut leanh::LeanObject,
    mut v_t_3366_: *mut leanh::LeanObject,
    mut v_h_3367_: *mut leanh::LeanObject,
    mut v_k_3368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3369_: u8 = 0;
    let mut v_res_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3369_ = (leanh::lean_unbox(v_t_3366_) as u8);
    v_res_3370_ = l_Std_Tactic_BVDecide_BVBinPred_ctorElim(
        v_motive_3364_,
        v_ctorIdx_3365_,
        v_t_boxed_3369_,
        v_h_3367_,
        v_k_3368_,
    );
    leanh::lean_dec(v_k_3368_);
    leanh::lean_dec(v_ctorIdx_3365_);
    return v_res_3370_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(
    mut v_eq_3371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_eq_3371_);
    return v_eq_3371_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg___boxed(
    mut v_eq_3372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim___redArg(v_eq_3372_);
    leanh::lean_dec(v_eq_3372_);
    return v_res_3373_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eq_elim(
    mut v_motive_3374_: *mut leanh::LeanObject,
    mut v_t_3375_: u8,
    mut v_h_3376_: *mut leanh::LeanObject,
    mut v_eq_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_eq_3377_);
    return v_eq_3377_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eq_elim___boxed(
    mut v_motive_3378_: *mut leanh::LeanObject,
    mut v_t_3379_: *mut leanh::LeanObject,
    mut v_h_3380_: *mut leanh::LeanObject,
    mut v_eq_3381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3382_: u8 = 0;
    let mut v_res_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3382_ = (leanh::lean_unbox(v_t_3379_) as u8);
    v_res_3383_ = l_Std_Tactic_BVDecide_BVBinPred_eq_elim(
        v_motive_3378_,
        v_t_boxed_3382_,
        v_h_3380_,
        v_eq_3381_,
    );
    leanh::lean_dec(v_eq_3381_);
    return v_res_3383_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(
    mut v_ult_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ult_3384_);
    return v_ult_3384_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg___boxed(
    mut v_ult_3385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim___redArg(v_ult_3385_);
    leanh::lean_dec(v_ult_3385_);
    return v_res_3386_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ult_elim(
    mut v_motive_3387_: *mut leanh::LeanObject,
    mut v_t_3388_: u8,
    mut v_h_3389_: *mut leanh::LeanObject,
    mut v_ult_3390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_ult_3390_);
    return v_ult_3390_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_ult_elim___boxed(
    mut v_motive_3391_: *mut leanh::LeanObject,
    mut v_t_3392_: *mut leanh::LeanObject,
    mut v_h_3393_: *mut leanh::LeanObject,
    mut v_ult_3394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_3395_: u8 = 0;
    let mut v_res_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_3395_ = (leanh::lean_unbox(v_t_3392_) as u8);
    v_res_3396_ = l_Std_Tactic_BVDecide_BVBinPred_ult_elim(
        v_motive_3391_,
        v_t_boxed_3395_,
        v_h_3393_,
        v_ult_3394_,
    );
    leanh::lean_dec(v_ult_3394_);
    return v_res_3396_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_toString(
    mut v_x_3399_: u8,
) -> *mut leanh::LeanObject {
    if v_x_3399_ == 0 {
        let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3400_ = l_Std_Tactic_BVDecide_BVBinPred_toString___closed__0;
        return v___x_3400_;
    } else {
        let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3401_ = l_Std_Tactic_BVDecide_BVBinPred_toString___closed__1;
        return v___x_3401_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(
    mut v_x_3402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_22__boxed_3403_: u8 = 0;
    let mut v_res_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_22__boxed_3403_ = (leanh::lean_unbox(v_x_3402_) as u8);
    v_res_3404_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_x_22__boxed_3403_);
    return v_res_3404_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(
    mut v_x_3407_: u8,
    mut v_a_3408_: *mut leanh::LeanObject,
    mut v_a_3409_: *mut leanh::LeanObject,
) -> u8 {
    if v_x_3407_ == 0 {
        let mut v___x_3410_: u8 = 0;
        v___x_3410_ = lean_nat_dec_eq(v_a_3408_, v_a_3409_);
        return v___x_3410_;
    } else {
        let mut v___x_3411_: u8 = 0;
        v___x_3411_ = lean_nat_dec_lt(v_a_3408_, v_a_3409_);
        return v___x_3411_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eval___redArg___boxed(
    mut v_x_3412_: *mut leanh::LeanObject,
    mut v_a_3413_: *mut leanh::LeanObject,
    mut v_a_3414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_100__boxed_3415_: u8 = 0;
    let mut v_res_3416_: u8 = 0;
    let mut v_r_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_100__boxed_3415_ = (leanh::lean_unbox(v_x_3412_) as u8);
    v_res_3416_ =
        l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_100__boxed_3415_, v_a_3413_, v_a_3414_);
    leanh::lean_dec(v_a_3414_);
    leanh::lean_dec(v_a_3413_);
    v_r_3417_ = leanh::lean_box((v_res_3416_) as usize);
    return v_r_3417_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eval(
    mut v_w_3418_: *mut leanh::LeanObject,
    mut v_x_3419_: u8,
    mut v_a_3420_: *mut leanh::LeanObject,
    mut v_a_3421_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3422_: u8 = 0;
    v___x_3422_ = l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_x_3419_, v_a_3420_, v_a_3421_);
    return v___x_3422_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(
    mut v_w_3423_: *mut leanh::LeanObject,
    mut v_x_3424_: *mut leanh::LeanObject,
    mut v_a_3425_: *mut leanh::LeanObject,
    mut v_a_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_113__boxed_3427_: u8 = 0;
    let mut v_res_3428_: u8 = 0;
    let mut v_r_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_113__boxed_3427_ = (leanh::lean_unbox(v_x_3424_) as u8);
    v_res_3428_ =
        l_Std_Tactic_BVDecide_BVBinPred_eval(v_w_3423_, v_x_113__boxed_3427_, v_a_3425_, v_a_3426_);
    leanh::lean_dec(v_a_3426_);
    leanh::lean_dec(v_a_3425_);
    leanh::lean_dec(v_w_3423_);
    v_r_3429_ = leanh::lean_box((v_res_3428_) as usize);
    return v_r_3429_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_ctorIdx(
    mut v_x_3430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3430_) == 0 {
        let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3431_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3431_;
    } else {
        let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3432_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3432_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_ctorIdx___boxed(
    mut v_x_3433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3434_ = l_Std_Tactic_BVDecide_BVPred_ctorIdx(v_x_3433_);
    leanh::lean_dec_ref(v_x_3433_);
    return v_res_3434_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(
    mut v_t_3435_: *mut leanh::LeanObject,
    mut v_k_3436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_3435_) == 0 {
        let mut v_w_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_op_3439_: u8 = 0;
        let mut v_rhs_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_w_3437_ = leanh::lean_ctor_get(v_t_3435_, 0);
        leanh::lean_inc(v_w_3437_);
        v_lhs_3438_ = leanh::lean_ctor_get(v_t_3435_, 1);
        leanh::lean_inc_ref(v_lhs_3438_);
        v_op_3439_ = leanh::lean_ctor_get_uint8(
            v_t_3435_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        );
        v_rhs_3440_ = leanh::lean_ctor_get(v_t_3435_, 2);
        leanh::lean_inc_ref(v_rhs_3440_);
        leanh::lean_dec_ref_known(v_t_3435_, 3);
        v___x_3441_ = leanh::lean_box((v_op_3439_) as usize);
        v___x_3442_ =
            leanh::lean_apply_4(v_k_3436_, v_w_3437_, v_lhs_3438_, v___x_3441_, v_rhs_3440_);
        return v___x_3442_;
    } else {
        let mut v_w_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_w_3443_ = leanh::lean_ctor_get(v_t_3435_, 0);
        leanh::lean_inc(v_w_3443_);
        v_expr_3444_ = leanh::lean_ctor_get(v_t_3435_, 1);
        leanh::lean_inc_ref(v_expr_3444_);
        v_idx_3445_ = leanh::lean_ctor_get(v_t_3435_, 2);
        leanh::lean_inc(v_idx_3445_);
        leanh::lean_dec_ref_known(v_t_3435_, 3);
        v___x_3446_ = leanh::lean_apply_3(v_k_3436_, v_w_3443_, v_expr_3444_, v_idx_3445_);
        return v___x_3446_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_ctorElim(
    mut v_motive_3447_: *mut leanh::LeanObject,
    mut v_ctorIdx_3448_: *mut leanh::LeanObject,
    mut v_t_3449_: *mut leanh::LeanObject,
    mut v_h_3450_: *mut leanh::LeanObject,
    mut v_k_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3452_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_3449_, v_k_3451_);
    return v___x_3452_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_ctorElim___boxed(
    mut v_motive_3453_: *mut leanh::LeanObject,
    mut v_ctorIdx_3454_: *mut leanh::LeanObject,
    mut v_t_3455_: *mut leanh::LeanObject,
    mut v_h_3456_: *mut leanh::LeanObject,
    mut v_k_3457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3458_ = l_Std_Tactic_BVDecide_BVPred_ctorElim(
        v_motive_3453_,
        v_ctorIdx_3454_,
        v_t_3455_,
        v_h_3456_,
        v_k_3457_,
    );
    leanh::lean_dec(v_ctorIdx_3454_);
    return v_res_3458_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_bin_elim___redArg(
    mut v_t_3459_: *mut leanh::LeanObject,
    mut v_bin_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3461_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_3459_, v_bin_3460_);
    return v___x_3461_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_bin_elim(
    mut v_motive_3462_: *mut leanh::LeanObject,
    mut v_t_3463_: *mut leanh::LeanObject,
    mut v_h_3464_: *mut leanh::LeanObject,
    mut v_bin_3465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3466_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_3463_, v_bin_3465_);
    return v___x_3466_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_getLsbD_elim___redArg(
    mut v_t_3467_: *mut leanh::LeanObject,
    mut v_getLsbD_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3469_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_3467_, v_getLsbD_3468_);
    return v___x_3469_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_getLsbD_elim(
    mut v_motive_3470_: *mut leanh::LeanObject,
    mut v_t_3471_: *mut leanh::LeanObject,
    mut v_h_3472_: *mut leanh::LeanObject,
    mut v_getLsbD_3473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_Std_Tactic_BVDecide_BVPred_ctorElim___redArg(v_t_3471_, v_getLsbD_3473_);
    return v___x_3474_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_toString(
    mut v_x_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3475_) == 0 {
        let mut v_w_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_op_3478_: u8 = 0;
        let mut v_rhs_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_w_3476_ = leanh::lean_ctor_get(v_x_3475_, 0);
        leanh::lean_inc_n(v_w_3476_, 2);
        v_lhs_3477_ = leanh::lean_ctor_get(v_x_3475_, 1);
        leanh::lean_inc_ref(v_lhs_3477_);
        v_op_3478_ = leanh::lean_ctor_get_uint8(
            v_x_3475_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        );
        v_rhs_3479_ = leanh::lean_ctor_get(v_x_3475_, 2);
        leanh::lean_inc_ref(v_rhs_3479_);
        leanh::lean_dec_ref_known(v_x_3475_, 3);
        v___x_3480_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__1;
        v___x_3481_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3476_, v_lhs_3477_);
        v___x_3482_ = lean_string_append(v___x_3480_, v___x_3481_);
        leanh::lean_dec_ref(v___x_3481_);
        v___x_3483_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__2;
        v___x_3484_ = lean_string_append(v___x_3482_, v___x_3483_);
        v___x_3485_ = l_Std_Tactic_BVDecide_BVBinPred_toString(v_op_3478_);
        v___x_3486_ = lean_string_append(v___x_3484_, v___x_3485_);
        leanh::lean_dec_ref(v___x_3485_);
        v___x_3487_ = lean_string_append(v___x_3486_, v___x_3483_);
        v___x_3488_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3476_, v_rhs_3479_);
        v___x_3489_ = lean_string_append(v___x_3487_, v___x_3488_);
        leanh::lean_dec_ref(v___x_3488_);
        v___x_3490_ = l_Std_Tactic_BVDecide_BVExpr_toString___closed__3;
        v___x_3491_ = lean_string_append(v___x_3489_, v___x_3490_);
        return v___x_3491_;
    } else {
        let mut v_w_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_w_3492_ = leanh::lean_ctor_get(v_x_3475_, 0);
        leanh::lean_inc(v_w_3492_);
        v_expr_3493_ = leanh::lean_ctor_get(v_x_3475_, 1);
        leanh::lean_inc_ref(v_expr_3493_);
        v_idx_3494_ = leanh::lean_ctor_get(v_x_3475_, 2);
        leanh::lean_inc(v_idx_3494_);
        leanh::lean_dec_ref_known(v_x_3475_, 3);
        v___x_3495_ = l_Std_Tactic_BVDecide_BVExpr_toString(v_w_3492_, v_expr_3493_);
        v___x_3496_ = l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__1;
        v___x_3497_ = lean_string_append(v___x_3495_, v___x_3496_);
        v___x_3498_ = l_Nat_reprFast(v_idx_3494_);
        v___x_3499_ = lean_string_append(v___x_3497_, v___x_3498_);
        leanh::lean_dec_ref(v___x_3498_);
        v___x_3500_ = l_Std_Tactic_BVDecide_instToStringBVBit___lam__0___closed__2;
        v___x_3501_ = lean_string_append(v___x_3499_, v___x_3500_);
        return v___x_3501_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_eval(
    mut v_assign_3504_: *mut leanh::LeanObject,
    mut v_x_3505_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_3505_) == 0 {
        let mut v_w_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_op_3508_: u8 = 0;
        let mut v_rhs_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3512_: u8 = 0;
        v_w_3506_ = leanh::lean_ctor_get(v_x_3505_, 0);
        leanh::lean_inc_n(v_w_3506_, 2);
        v_lhs_3507_ = leanh::lean_ctor_get(v_x_3505_, 1);
        leanh::lean_inc_ref(v_lhs_3507_);
        v_op_3508_ = leanh::lean_ctor_get_uint8(
            v_x_3505_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        );
        v_rhs_3509_ = leanh::lean_ctor_get(v_x_3505_, 2);
        leanh::lean_inc_ref(v_rhs_3509_);
        leanh::lean_dec_ref_known(v_x_3505_, 3);
        v___x_3510_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3506_, v_assign_3504_, v_lhs_3507_);
        v___x_3511_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3506_, v_assign_3504_, v_rhs_3509_);
        v___x_3512_ =
            l_Std_Tactic_BVDecide_BVBinPred_eval___redArg(v_op_3508_, v___x_3510_, v___x_3511_);
        leanh::lean_dec(v___x_3511_);
        leanh::lean_dec(v___x_3510_);
        return v___x_3512_;
    } else {
        let mut v_w_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3517_: u8 = 0;
        v_w_3513_ = leanh::lean_ctor_get(v_x_3505_, 0);
        leanh::lean_inc(v_w_3513_);
        v_expr_3514_ = leanh::lean_ctor_get(v_x_3505_, 1);
        leanh::lean_inc_ref(v_expr_3514_);
        v_idx_3515_ = leanh::lean_ctor_get(v_x_3505_, 2);
        leanh::lean_inc(v_idx_3515_);
        leanh::lean_dec_ref_known(v_x_3505_, 3);
        v___x_3516_ = l_Std_Tactic_BVDecide_BVExpr_eval(v_w_3513_, v_assign_3504_, v_expr_3514_);
        v___x_3517_ = l_Nat_testBit(v___x_3516_, v_idx_3515_);
        leanh::lean_dec(v_idx_3515_);
        leanh::lean_dec(v___x_3516_);
        return v___x_3517_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_eval___boxed(
    mut v_assign_3518_: *mut leanh::LeanObject,
    mut v_x_3519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3520_: u8 = 0;
    let mut v_r_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_3518_, v_x_3519_);
    leanh::lean_dec_ref(v_assign_3518_);
    v_r_3521_ = leanh::lean_box((v_res_3520_) as usize);
    return v_r_3521_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(
    mut v_assign_3522_: *mut leanh::LeanObject,
    mut v_x_3523_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3524_: u8 = 0;
    v___x_3524_ = l_Std_Tactic_BVDecide_BVPred_eval(v_assign_3522_, v_x_3523_);
    return v___x_3524_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(
    mut v_assign_3525_: *mut leanh::LeanObject,
    mut v_x_3526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3527_: u8 = 0;
    let mut v_r_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(v_assign_3525_, v_x_3526_);
    leanh::lean_dec_ref(v_assign_3525_);
    v_r_3528_ = leanh::lean_box((v_res_3527_) as usize);
    return v_r_3528_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVLogicalExpr_eval(
    mut v_assign_3529_: *mut leanh::LeanObject,
    mut v_expr_3530_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: u8 = 0;
    v___f_3531_ = leanh::lean_alloc_closure(
        l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3531_, 0, v_assign_3529_);
    v___x_3532_ = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(v___f_3531_, v_expr_3530_);
    return v___x_3532_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(
    mut v_assign_3533_: *mut leanh::LeanObject,
    mut v_expr_3534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3535_: u8 = 0;
    let mut v_r_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3535_ = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(v_assign_3533_, v_expr_3534_);
    v_r_3536_ = leanh::lean_box((v_res_3535_) as usize);
    return v_r_3536_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Tactic_BVDecide_instInhabitedBVBit = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit();
    leanh::lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Hashable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
}