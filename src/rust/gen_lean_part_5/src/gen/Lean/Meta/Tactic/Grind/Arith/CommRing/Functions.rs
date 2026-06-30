// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
use crate::ffi::lean_st_ref_get;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr2;
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Nat_mkType, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_isDefEqI;
use crate::r#gen::Lean::Meta::Sym::Arith::MonadCanon::l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::MonadRing::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_internalize___boxed;
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value:
    leanh::LeanStringObject<64> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 64,
    m_capacity: 64,
    m_length: 63,
    m_data: [
        101, 114, 114, 111, 114, 32, 119, 104, 105, 108, 101, 32, 105, 110, 105, 116, 105, 97, 108,
        105, 122, 105, 110, 103, 32, 96, 103, 114, 105, 110, 100, 32, 114, 105, 110, 103, 96, 32,
        111, 112, 101, 114, 97, 116, 111, 114, 115, 58, 10, 105, 110, 115, 116, 97, 110, 99, 101,
        32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value:
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
    m_data: [96, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value:
    leanh::LeanStringObject<50> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        10, 105, 115, 32, 110, 111, 116, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97,
        108, 108, 121, 32, 101, 113, 117, 97, 108, 32, 116, 111, 32, 116, 104, 101, 32, 101, 120,
        112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value:
    leanh::LeanStringObject<59> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 59,
    m_capacity: 59,
    m_length: 58,
    m_data: [
        10, 119, 104, 101, 110, 32, 111, 110, 108, 121, 32, 114, 101, 100, 117, 99, 105, 98, 108,
        101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 97, 110, 100, 32, 105,
        110, 115, 116, 97, 110, 99, 101, 115, 32, 97, 114, 101, 32, 114, 101, 100, 117, 99, 101,
        100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value:
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
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value:
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
    m_data: [110, 112, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut leanh::LeanObject,
        12050285396929189622 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__3_value
        ) as *mut leanh::LeanObject,
        18388652353510661091 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value:
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
    m_data: [104, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value:
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
    m_data: [72, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        12847922472053947547 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value:
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
    m_data: [110, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut leanh::LeanObject,
        12050285396929189622 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        14765357657372582228 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value:
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
    m_data: [78, 97, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        5779414593499529281 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        9594062259507646949 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut leanh::LeanObject,
        12050285396929189622 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        5442360487226035463 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
        ) as *mut leanh::LeanObject,
        10393083817453678557 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__4_value
        ) as *mut leanh::LeanObject,
        10393083817453678557 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__6_value
        ) as *mut leanh::LeanObject,
        10680564408669940870 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        10135981711945425184 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value:
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
    m_data: [82, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value:
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
    m_data: [116, 111, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        10806710915646349764 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__3_value
        ) as *mut leanh::LeanObject,
        18169824201013588232 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value:
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
    m_data: [72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
        ) as *mut leanh::LeanObject,
        16856108565602861689 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value:
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
    m_data: [104, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__5_value
        ) as *mut leanh::LeanObject,
        16856108565602861689 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__7_value
        ) as *mut leanh::LeanObject,
        4187025665268973031 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        18134279130838690737 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value:
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
    m_data: [116, 111, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value
        ) as *mut leanh::LeanObject,
        12050285396929189622 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        7102027102192867304 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
        ) as *mut leanh::LeanObject,
        2929883540436775422 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__4_value
        ) as *mut leanh::LeanObject,
        2929883540436775422 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__6_value
        ) as *mut leanh::LeanObject,
        1611444129324655608 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value:
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
    m_data: [116, 111, 78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        10806710915646349764 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        10040236838748678500 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        9626815015619986526 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        9626815015619986526 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__4_value
        ) as *mut leanh::LeanObject,
        17185717442815859305 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value:
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
    m_data: [99, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__0_value
        ) as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__1_value
        ) as *mut leanh::LeanObject,
        439118677539554485 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value:
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
    m_data: [105, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__2_value
        ) as *mut leanh::LeanObject,
        10806710915646349764 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0_value
        ) as *mut leanh::LeanObject,
        14561037289535094017 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value:
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
    m_data: [73, 110, 116, 67, 97, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2_value
        ) as *mut leanh::LeanObject,
        4977321555018234431 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut leanh::LeanObject,9341924117480681831 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__3_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__1_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value:
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
    m_data: [70, 105, 101, 108, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value:
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
    m_data: [116, 111, 73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__1_value
        ) as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        8615353994042975301 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__1_value
        ) as *mut leanh::LeanObject,
        7723290638220826725 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value:
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
    m_data: [73, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
        ) as *mut leanh::LeanObject,
        1412621069384631438 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value:
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
    m_data: [105, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__3_value
        ) as *mut leanh::LeanObject,
        1412621069384631438 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__5_value
        ) as *mut leanh::LeanObject,
        10171450186735820607 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32,
        102, 105, 101, 108, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(
    mut v_msgData_1299_: *mut leanh::LeanObject,
    mut v___y_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = lean_st_ref_get(v___y_1303_);
    v_env_1306_ = leanh::lean_ctor_get(v___x_1305_, 0);
    leanh::lean_inc_ref(v_env_1306_);
    leanh::lean_dec(v___x_1305_);
    v___x_1307_ = lean_st_ref_get(v___y_1301_);
    v_mctx_1308_ = leanh::lean_ctor_get(v___x_1307_, 0);
    leanh::lean_inc_ref(v_mctx_1308_);
    leanh::lean_dec(v___x_1307_);
    v_lctx_1309_ = leanh::lean_ctor_get(v___y_1300_, 2);
    v_options_1310_ = leanh::lean_ctor_get(v___y_1302_, 2);
    leanh::lean_inc_ref(v_options_1310_);
    leanh::lean_inc_ref(v_lctx_1309_);
    v___x_1311_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1311_, 0, v_env_1306_);
    leanh::lean_ctor_set(v___x_1311_, 1, v_mctx_1308_);
    leanh::lean_ctor_set(v___x_1311_, 2, v_lctx_1309_);
    leanh::lean_ctor_set(v___x_1311_, 3, v_options_1310_);
    v___x_1312_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1312_, 0, v___x_1311_);
    leanh::lean_ctor_set(v___x_1312_, 1, v_msgData_1299_);
    v___x_1313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1313_, 0, v___x_1312_);
    return v___x_1313_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0___boxed(
    mut v_msgData_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msgData_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
    leanh::lean_dec(v___y_1318_);
    leanh::lean_dec_ref(v___y_1317_);
    leanh::lean_dec(v___y_1316_);
    leanh::lean_dec_ref(v___y_1315_);
    return v_res_1320_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(
    mut v_msg_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1327_ = leanh::lean_ctor_get(v___y_1324_, 5);
                v___x_1328_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0_spec__0(v_msg_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
                v_a_1329_ = leanh::lean_ctor_get(v___x_1328_, 0);
                v_isSharedCheck_1337_ = (!leanh::lean_is_exclusive(v___x_1328_)) as u8;
                if v_isSharedCheck_1337_ == 0 {
                    v___x_1331_ = v___x_1328_;
                    v_isShared_1332_ = v_isSharedCheck_1337_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1329_);
                    leanh::lean_dec(v___x_1328_);
                    v___x_1331_ = leanh::lean_box(0);
                    v_isShared_1332_ = v_isSharedCheck_1337_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1327_);
                v___x_1333_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1333_, 0, v_ref_1327_);
                leanh::lean_ctor_set(v___x_1333_, 1, v_a_1329_);
                if v_isShared_1332_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1331_, 1);
                    leanh::lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
                    v___x_1335_ = v_reuseFailAlloc_1336_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg___boxed(
    mut v_msg_1338_: *mut leanh::LeanObject,
    mut v___y_1339_: *mut leanh::LeanObject,
    mut v___y_1340_: *mut leanh::LeanObject,
    mut v___y_1341_: *mut leanh::LeanObject,
    mut v___y_1342_: *mut leanh::LeanObject,
    mut v___y_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(
            v_msg_1338_,
            v___y_1339_,
            v___y_1340_,
            v___y_1341_,
            v___y_1342_,
        );
    leanh::lean_dec(v___y_1342_);
    leanh::lean_dec_ref(v___y_1341_);
    leanh::lean_dec(v___y_1340_);
    leanh::lean_dec_ref(v___y_1339_);
    return v_res_1344_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1346_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__0;
    v___x_1347_ = l_Lean_stringToMessageData(v___x_1346_);
    return v___x_1347_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1349_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__2;
    v___x_1350_ = l_Lean_stringToMessageData(v___x_1349_);
    return v___x_1350_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__4;
    v___x_1353_ = l_Lean_stringToMessageData(v___x_1352_);
    return v___x_1353_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1355_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__6;
    v___x_1356_ = l_Lean_stringToMessageData(v___x_1355_);
    return v___x_1356_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkInst(
    mut v_declName_1357_: *mut leanh::LeanObject,
    mut v_inst_1358_: *mut leanh::LeanObject,
    mut v_inst_x27_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
    mut v_a_1361_: *mut leanh::LeanObject,
    mut v_a_1362_: *mut leanh::LeanObject,
    mut v_a_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut v_a_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1393_: u8 = 0;
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_inst_x27_1359_);
                leanh::lean_inc_ref(v_inst_1358_);
                v___x_1365_ = l_Lean_Meta_isDefEqI(
                    v_inst_1358_,
                    v_inst_x27_1359_,
                    v_a_1360_,
                    v_a_1361_,
                    v_a_1362_,
                    v_a_1363_,
                );
                if leanh::lean_obj_tag(v___x_1365_) == 0 {
                    v_a_1366_ = leanh::lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1389_ = (!leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1368_ = v___x_1365_;
                        v_isShared_1369_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1366_);
                        leanh::lean_dec(v___x_1365_);
                        v___x_1368_ = leanh::lean_box(0);
                        v_isShared_1369_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_inst_x27_1359_);
                    leanh::lean_dec_ref(v_inst_1358_);
                    leanh::lean_dec(v_declName_1357_);
                    v_a_1390_ = leanh::lean_ctor_get(v___x_1365_, 0);
                    v_isSharedCheck_1397_ = (!leanh::lean_is_exclusive(v___x_1365_)) as u8;
                    if v_isSharedCheck_1397_ == 0 {
                        v___x_1392_ = v___x_1365_;
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1390_);
                        leanh::lean_dec(v___x_1365_);
                        v___x_1392_ = leanh::lean_box(0);
                        v_isShared_1393_ = v_isSharedCheck_1397_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1370_ = (leanh::lean_unbox(v_a_1366_) as u8);
                leanh::lean_dec(v_a_1366_);
                if v___x_1370_ == 0 {
                    leanh::lean_del_object(v___x_1368_);
                    v___x_1371_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__1,
                    );
                    v___x_1372_ = l_Lean_MessageData_ofName(v_declName_1357_);
                    v___x_1373_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1373_, 0, v___x_1371_);
                    leanh::lean_ctor_set(v___x_1373_, 1, v___x_1372_);
                    v___x_1374_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__3,
                    );
                    v___x_1375_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1375_, 0, v___x_1373_);
                    leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
                    v___x_1376_ = l_Lean_indentExpr(v_inst_1358_);
                    v___x_1377_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1377_, 0, v___x_1375_);
                    leanh::lean_ctor_set(v___x_1377_, 1, v___x_1376_);
                    v___x_1378_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__5,
                    );
                    v___x_1379_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1379_, 0, v___x_1377_);
                    leanh::lean_ctor_set(v___x_1379_, 1, v___x_1378_);
                    v___x_1380_ = l_Lean_indentExpr(v_inst_x27_1359_);
                    v___x_1381_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1381_, 0, v___x_1379_);
                    leanh::lean_ctor_set(v___x_1381_, 1, v___x_1380_);
                    v___x_1382_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_checkInst___closed__7,
                    );
                    v___x_1383_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1383_, 0, v___x_1381_);
                    leanh::lean_ctor_set(v___x_1383_, 1, v___x_1382_);
                    v___x_1384_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(v___x_1383_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
                    return v___x_1384_;
                } else {
                    leanh::lean_dec_ref(v_inst_x27_1359_);
                    leanh::lean_dec_ref(v_inst_1358_);
                    leanh::lean_dec(v_declName_1357_);
                    v___x_1385_ = leanh::lean_box(0);
                    if v_isShared_1369_ == 0 {
                        leanh::lean_ctor_set(v___x_1368_, 0, v___x_1385_);
                        v___x_1387_ = v___x_1368_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
                        v___x_1387_ = v_reuseFailAlloc_1388_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1387_;
            }
            3 => {
                if v_isShared_1393_ == 0 {
                    v___x_1395_ = v___x_1392_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
                    v___x_1395_ = v_reuseFailAlloc_1396_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1395_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed(
    mut v_declName_1398_: *mut leanh::LeanObject,
    mut v_inst_1399_: *mut leanh::LeanObject,
    mut v_inst_x27_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
    mut v_a_1404_: *mut leanh::LeanObject,
    mut v_a_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
        v_declName_1398_,
        v_inst_1399_,
        v_inst_x27_1400_,
        v_a_1401_,
        v_a_1402_,
        v_a_1403_,
        v_a_1404_,
    );
    leanh::lean_dec(v_a_1404_);
    leanh::lean_dec_ref(v_a_1403_);
    leanh::lean_dec(v_a_1402_);
    leanh::lean_dec_ref(v_a_1401_);
    return v_res_1406_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(
    mut v_00_u03b1_1407_: *mut leanh::LeanObject,
    mut v_msg_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
    mut v___y_1410_: *mut leanh::LeanObject,
    mut v___y_1411_: *mut leanh::LeanObject,
    mut v___y_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___redArg(
            v_msg_1408_,
            v___y_1409_,
            v___y_1410_,
            v___y_1411_,
            v___y_1412_,
        );
    return v___x_1414_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0___boxed(
    mut v_00_u03b1_1415_: *mut leanh::LeanObject,
    mut v_msg_1416_: *mut leanh::LeanObject,
    mut v___y_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
    mut v___y_1419_: *mut leanh::LeanObject,
    mut v___y_1420_: *mut leanh::LeanObject,
    mut v___y_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_checkInst_spec__0(
        v_00_u03b1_1415_,
        v_msg_1416_,
        v___y_1417_,
        v___y_1418_,
        v___y_1419_,
        v___y_1420_,
    );
    leanh::lean_dec(v___y_1420_);
    leanh::lean_dec_ref(v___y_1419_);
    leanh::lean_dec(v___y_1418_);
    leanh::lean_dec_ref(v___y_1417_);
    return v_res_1422_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0(
    mut v_inst_1423_: *mut leanh::LeanObject,
    mut v_declName_1424_: *mut leanh::LeanObject,
    mut v___x_1425_: *mut leanh::LeanObject,
    mut v_type_1426_: *mut leanh::LeanObject,
    mut v_inst_1427_: *mut leanh::LeanObject,
    mut v_____r_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonExpr_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1429_ = leanh::lean_ctor_get(v_inst_1423_, 0);
    leanh::lean_inc(v_canonExpr_1429_);
    leanh::lean_dec_ref(v_inst_1423_);
    v___x_1430_ = l_Lean_mkConst(v_declName_1424_, v___x_1425_);
    v___x_1431_ = l_Lean_mkAppB(v___x_1430_, v_type_1426_, v_inst_1427_);
    v___x_1432_ = leanh::lean_apply_1(v_canonExpr_1429_, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1(
    mut v_inst_1433_: *mut leanh::LeanObject,
    mut v_declName_1434_: *mut leanh::LeanObject,
    mut v___x_1435_: *mut leanh::LeanObject,
    mut v_type_1436_: *mut leanh::LeanObject,
    mut v_expectedInst_1437_: *mut leanh::LeanObject,
    mut v_inst_1438_: *mut leanh::LeanObject,
    mut v_toBind_1439_: *mut leanh::LeanObject,
    mut v_inst_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1440_);
    leanh::lean_inc(v_declName_1434_);
    v___f_1441_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1441_, 0, v_inst_1433_);
    leanh::lean_closure_set(v___f_1441_, 1, v_declName_1434_);
    leanh::lean_closure_set(v___f_1441_, 2, v___x_1435_);
    leanh::lean_closure_set(v___f_1441_, 3, v_type_1436_);
    leanh::lean_closure_set(v___f_1441_, 4, v_inst_1440_);
    v___x_1442_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1442_, 0, v_declName_1434_);
    leanh::lean_closure_set(v___x_1442_, 1, v_inst_1440_);
    leanh::lean_closure_set(v___x_1442_, 2, v_expectedInst_1437_);
    v___x_1443_ = leanh::lean_apply_2(v_inst_1438_, leanh::lean_box(0), v___x_1442_);
    v___x_1444_ = leanh::lean_apply_4(
        v_toBind_1439_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1443_,
        v___f_1441_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(
    mut v_inst_1445_: *mut leanh::LeanObject,
    mut v_inst_1446_: *mut leanh::LeanObject,
    mut v_inst_1447_: *mut leanh::LeanObject,
    mut v_inst_1448_: *mut leanh::LeanObject,
    mut v_type_1449_: *mut leanh::LeanObject,
    mut v_u_1450_: *mut leanh::LeanObject,
    mut v_instDeclName_1451_: *mut leanh::LeanObject,
    mut v_declName_1452_: *mut leanh::LeanObject,
    mut v_expectedInst_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1454_ = leanh::lean_ctor_get(v_inst_1447_, 1);
    leanh::lean_inc_n(v_toBind_1454_, 2);
    v___x_1455_ = leanh::lean_box(0);
    v___x_1456_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1456_, 0, v_u_1450_);
    leanh::lean_ctor_set(v___x_1456_, 1, v___x_1455_);
    leanh::lean_inc_ref(v_type_1449_);
    leanh::lean_inc_ref(v___x_1456_);
    leanh::lean_inc_ref(v_inst_1448_);
    v___f_1457_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1457_, 0, v_inst_1448_);
    leanh::lean_closure_set(v___f_1457_, 1, v_declName_1452_);
    leanh::lean_closure_set(v___f_1457_, 2, v___x_1456_);
    leanh::lean_closure_set(v___f_1457_, 3, v_type_1449_);
    leanh::lean_closure_set(v___f_1457_, 4, v_expectedInst_1453_);
    leanh::lean_closure_set(v___f_1457_, 5, v_inst_1445_);
    leanh::lean_closure_set(v___f_1457_, 6, v_toBind_1454_);
    v___x_1458_ = l_Lean_mkConst(v_instDeclName_1451_, v___x_1456_);
    v___x_1459_ = l_Lean_Expr_app___override(v___x_1458_, v_type_1449_);
    v___x_1460_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1447_,
        v_inst_1446_,
        v_inst_1448_,
        v___x_1459_,
    );
    v___x_1461_ = leanh::lean_apply_4(
        v_toBind_1454_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1460_,
        v___f_1457_,
    );
    return v___x_1461_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn(
    mut v_m_1462_: *mut leanh::LeanObject,
    mut v_inst_1463_: *mut leanh::LeanObject,
    mut v_inst_1464_: *mut leanh::LeanObject,
    mut v_inst_1465_: *mut leanh::LeanObject,
    mut v_inst_1466_: *mut leanh::LeanObject,
    mut v_type_1467_: *mut leanh::LeanObject,
    mut v_u_1468_: *mut leanh::LeanObject,
    mut v_instDeclName_1469_: *mut leanh::LeanObject,
    mut v_declName_1470_: *mut leanh::LeanObject,
    mut v_expectedInst_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1472_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(
        v_inst_1463_,
        v_inst_1464_,
        v_inst_1465_,
        v_inst_1466_,
        v_type_1467_,
        v_u_1468_,
        v_instDeclName_1469_,
        v_declName_1470_,
        v_expectedInst_1471_,
    );
    return v___x_1472_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0(
    mut v_inst_1473_: *mut leanh::LeanObject,
    mut v_declName_1474_: *mut leanh::LeanObject,
    mut v___x_1475_: *mut leanh::LeanObject,
    mut v_type_1476_: *mut leanh::LeanObject,
    mut v_inst_1477_: *mut leanh::LeanObject,
    mut v_____r_1478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonExpr_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1479_ = leanh::lean_ctor_get(v_inst_1473_, 0);
    leanh::lean_inc(v_canonExpr_1479_);
    leanh::lean_dec_ref(v_inst_1473_);
    v___x_1480_ = l_Lean_mkConst(v_declName_1474_, v___x_1475_);
    leanh::lean_inc_ref_n(v_type_1476_, 2);
    v___x_1481_ = l_Lean_mkApp4(
        v___x_1480_,
        v_type_1476_,
        v_type_1476_,
        v_type_1476_,
        v_inst_1477_,
    );
    v___x_1482_ = leanh::lean_apply_1(v_canonExpr_1479_, v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1(
    mut v_inst_1483_: *mut leanh::LeanObject,
    mut v_declName_1484_: *mut leanh::LeanObject,
    mut v___x_1485_: *mut leanh::LeanObject,
    mut v_type_1486_: *mut leanh::LeanObject,
    mut v_expectedInst_1487_: *mut leanh::LeanObject,
    mut v_inst_1488_: *mut leanh::LeanObject,
    mut v_toBind_1489_: *mut leanh::LeanObject,
    mut v_inst_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_1490_);
    leanh::lean_inc(v_declName_1484_);
    v___f_1491_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_1491_, 0, v_inst_1483_);
    leanh::lean_closure_set(v___f_1491_, 1, v_declName_1484_);
    leanh::lean_closure_set(v___f_1491_, 2, v___x_1485_);
    leanh::lean_closure_set(v___f_1491_, 3, v_type_1486_);
    leanh::lean_closure_set(v___f_1491_, 4, v_inst_1490_);
    v___x_1492_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1492_, 0, v_declName_1484_);
    leanh::lean_closure_set(v___x_1492_, 1, v_inst_1490_);
    leanh::lean_closure_set(v___x_1492_, 2, v_expectedInst_1487_);
    v___x_1493_ = leanh::lean_apply_2(v_inst_1488_, leanh::lean_box(0), v___x_1492_);
    v___x_1494_ = leanh::lean_apply_4(
        v_toBind_1489_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1493_,
        v___f_1491_,
    );
    return v___x_1494_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
    mut v_inst_1495_: *mut leanh::LeanObject,
    mut v_inst_1496_: *mut leanh::LeanObject,
    mut v_inst_1497_: *mut leanh::LeanObject,
    mut v_inst_1498_: *mut leanh::LeanObject,
    mut v_type_1499_: *mut leanh::LeanObject,
    mut v_u_1500_: *mut leanh::LeanObject,
    mut v_instDeclName_1501_: *mut leanh::LeanObject,
    mut v_declName_1502_: *mut leanh::LeanObject,
    mut v_expectedInst_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1504_ = leanh::lean_ctor_get(v_inst_1497_, 1);
    leanh::lean_inc_n(v_toBind_1504_, 2);
    v___x_1505_ = leanh::lean_box(0);
    leanh::lean_inc_n(v_u_1500_, 2);
    v___x_1506_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1506_, 0, v_u_1500_);
    leanh::lean_ctor_set(v___x_1506_, 1, v___x_1505_);
    v___x_1507_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1507_, 0, v_u_1500_);
    leanh::lean_ctor_set(v___x_1507_, 1, v___x_1506_);
    v___x_1508_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1508_, 0, v_u_1500_);
    leanh::lean_ctor_set(v___x_1508_, 1, v___x_1507_);
    leanh::lean_inc_ref_n(v_type_1499_, 3);
    leanh::lean_inc_ref(v___x_1508_);
    leanh::lean_inc_ref(v_inst_1498_);
    v___f_1509_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg___lam__1 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1509_, 0, v_inst_1498_);
    leanh::lean_closure_set(v___f_1509_, 1, v_declName_1502_);
    leanh::lean_closure_set(v___f_1509_, 2, v___x_1508_);
    leanh::lean_closure_set(v___f_1509_, 3, v_type_1499_);
    leanh::lean_closure_set(v___f_1509_, 4, v_expectedInst_1503_);
    leanh::lean_closure_set(v___f_1509_, 5, v_inst_1495_);
    leanh::lean_closure_set(v___f_1509_, 6, v_toBind_1504_);
    v___x_1510_ = l_Lean_mkConst(v_instDeclName_1501_, v___x_1508_);
    v___x_1511_ = l_Lean_mkApp3(v___x_1510_, v_type_1499_, v_type_1499_, v_type_1499_);
    v___x_1512_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1497_,
        v_inst_1496_,
        v_inst_1498_,
        v___x_1511_,
    );
    v___x_1513_ = leanh::lean_apply_4(
        v_toBind_1504_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1512_,
        v___f_1509_,
    );
    return v___x_1513_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn(
    mut v_m_1514_: *mut leanh::LeanObject,
    mut v_inst_1515_: *mut leanh::LeanObject,
    mut v_inst_1516_: *mut leanh::LeanObject,
    mut v_inst_1517_: *mut leanh::LeanObject,
    mut v_inst_1518_: *mut leanh::LeanObject,
    mut v_type_1519_: *mut leanh::LeanObject,
    mut v_u_1520_: *mut leanh::LeanObject,
    mut v_instDeclName_1521_: *mut leanh::LeanObject,
    mut v_declName_1522_: *mut leanh::LeanObject,
    mut v_expectedInst_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1524_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
        v_inst_1515_,
        v_inst_1516_,
        v_inst_1517_,
        v_inst_1518_,
        v_type_1519_,
        v_u_1520_,
        v_instDeclName_1521_,
        v_declName_1522_,
        v_expectedInst_1523_,
    );
    return v___x_1524_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0(
    mut v_inst_1525_: *mut leanh::LeanObject,
    mut v___x_1526_: *mut leanh::LeanObject,
    mut v___x_1527_: *mut leanh::LeanObject,
    mut v_type_1528_: *mut leanh::LeanObject,
    mut v___x_1529_: *mut leanh::LeanObject,
    mut v_inst_1530_: *mut leanh::LeanObject,
    mut v_____r_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonExpr_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonExpr_1532_ = leanh::lean_ctor_get(v_inst_1525_, 0);
    leanh::lean_inc(v_canonExpr_1532_);
    leanh::lean_dec_ref(v_inst_1525_);
    v___x_1533_ = l_Lean_mkConst(v___x_1526_, v___x_1527_);
    leanh::lean_inc_ref(v_type_1528_);
    v___x_1534_ = l_Lean_mkApp4(
        v___x_1533_,
        v_type_1528_,
        v___x_1529_,
        v_type_1528_,
        v_inst_1530_,
    );
    v___x_1535_ = leanh::lean_apply_1(v_canonExpr_1532_, v___x_1534_);
    return v___x_1535_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1(
    mut v___x_1546_: *mut leanh::LeanObject,
    mut v_type_1547_: *mut leanh::LeanObject,
    mut v_semiringInst_1548_: *mut leanh::LeanObject,
    mut v___x_1549_: *mut leanh::LeanObject,
    mut v_inst_1550_: *mut leanh::LeanObject,
    mut v___x_1551_: *mut leanh::LeanObject,
    mut v___x_1552_: *mut leanh::LeanObject,
    mut v_inst_1553_: *mut leanh::LeanObject,
    mut v_toBind_1554_: *mut leanh::LeanObject,
    mut v_inst_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__4;
    v___x_1557_ = l_Lean_mkConst(v___x_1556_, v___x_1546_);
    leanh::lean_inc_ref(v_type_1547_);
    v_inst_x27_1558_ = l_Lean_mkAppB(v___x_1557_, v_type_1547_, v_semiringInst_1548_);
    v___x_1559_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1___closed__5;
    v___x_1560_ = l_Lean_Name_mkStr2(v___x_1549_, v___x_1559_);
    leanh::lean_inc_ref(v_inst_1555_);
    leanh::lean_inc(v___x_1560_);
    v___f_1561_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_1561_, 0, v_inst_1550_);
    leanh::lean_closure_set(v___f_1561_, 1, v___x_1560_);
    leanh::lean_closure_set(v___f_1561_, 2, v___x_1551_);
    leanh::lean_closure_set(v___f_1561_, 3, v_type_1547_);
    leanh::lean_closure_set(v___f_1561_, 4, v___x_1552_);
    leanh::lean_closure_set(v___f_1561_, 5, v_inst_1555_);
    v___x_1562_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_1562_, 0, v___x_1560_);
    leanh::lean_closure_set(v___x_1562_, 1, v_inst_1555_);
    leanh::lean_closure_set(v___x_1562_, 2, v_inst_x27_1558_);
    v___x_1563_ = leanh::lean_apply_2(v_inst_1553_, leanh::lean_box(0), v___x_1562_);
    v___x_1564_ = leanh::lean_apply_4(
        v_toBind_1554_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1563_,
        v___f_1561_,
    );
    return v___x_1564_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = leanh::lean_unsigned_to_nat(0);
    v___x_1569_ = l_Lean_Level_ofNat(v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
    mut v_inst_1570_: *mut leanh::LeanObject,
    mut v_inst_1571_: *mut leanh::LeanObject,
    mut v_inst_1572_: *mut leanh::LeanObject,
    mut v_inst_1573_: *mut leanh::LeanObject,
    mut v_u_1574_: *mut leanh::LeanObject,
    mut v_type_1575_: *mut leanh::LeanObject,
    mut v_semiringInst_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1577_ = leanh::lean_ctor_get(v_inst_1572_, 1);
    leanh::lean_inc_n(v_toBind_1577_, 2);
    v___x_1578_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__0;
    v___x_1579_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__1;
    v___x_1580_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___closed__2,
    );
    v___x_1581_ = leanh::lean_box(0);
    leanh::lean_inc(v_u_1574_);
    v___x_1582_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1582_, 0, v_u_1574_);
    leanh::lean_ctor_set(v___x_1582_, 1, v___x_1581_);
    leanh::lean_inc_ref(v___x_1582_);
    v___x_1583_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1583_, 0, v___x_1580_);
    leanh::lean_ctor_set(v___x_1583_, 1, v___x_1582_);
    v___x_1584_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1584_, 0, v_u_1574_);
    leanh::lean_ctor_set(v___x_1584_, 1, v___x_1583_);
    leanh::lean_inc_ref(v___x_1584_);
    v___x_1585_ = l_Lean_mkConst(v___x_1579_, v___x_1584_);
    v___x_1586_ = l_Lean_Nat_mkType;
    leanh::lean_inc_ref(v_inst_1573_);
    leanh::lean_inc_ref_n(v_type_1575_, 2);
    v___f_1587_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_1587_, 0, v___x_1582_);
    leanh::lean_closure_set(v___f_1587_, 1, v_type_1575_);
    leanh::lean_closure_set(v___f_1587_, 2, v_semiringInst_1576_);
    leanh::lean_closure_set(v___f_1587_, 3, v___x_1578_);
    leanh::lean_closure_set(v___f_1587_, 4, v_inst_1573_);
    leanh::lean_closure_set(v___f_1587_, 5, v___x_1584_);
    leanh::lean_closure_set(v___f_1587_, 6, v___x_1586_);
    leanh::lean_closure_set(v___f_1587_, 7, v_inst_1570_);
    leanh::lean_closure_set(v___f_1587_, 8, v_toBind_1577_);
    v___x_1588_ = l_Lean_mkApp3(v___x_1585_, v_type_1575_, v___x_1586_, v_type_1575_);
    v___x_1589_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(
        v_inst_1572_,
        v_inst_1571_,
        v_inst_1573_,
        v___x_1588_,
    );
    v___x_1590_ = leanh::lean_apply_4(
        v_toBind_1577_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1589_,
        v___f_1587_,
    );
    return v___x_1590_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn(
    mut v_m_1591_: *mut leanh::LeanObject,
    mut v_inst_1592_: *mut leanh::LeanObject,
    mut v_inst_1593_: *mut leanh::LeanObject,
    mut v_inst_1594_: *mut leanh::LeanObject,
    mut v_inst_1595_: *mut leanh::LeanObject,
    mut v_u_1596_: *mut leanh::LeanObject,
    mut v_type_1597_: *mut leanh::LeanObject,
    mut v_semiringInst_1598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
        v_inst_1592_,
        v_inst_1593_,
        v_inst_1594_,
        v_inst_1595_,
        v_u_1596_,
        v_type_1597_,
        v_semiringInst_1598_,
    );
    return v___x_1599_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0(
    mut v___x_1600_: *mut leanh::LeanObject,
    mut v___x_1601_: *mut leanh::LeanObject,
    mut v___x_1602_: *mut leanh::LeanObject,
    mut v_type_1603_: *mut leanh::LeanObject,
    mut v_canonExpr_1604_: *mut leanh::LeanObject,
    mut v_inst_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_Name_mkStr2(v___x_1600_, v___x_1601_);
    v___x_1607_ = l_Lean_mkConst(v___x_1606_, v___x_1602_);
    v___x_1608_ = l_Lean_mkAppB(v___x_1607_, v_type_1603_, v_inst_1605_);
    v___x_1609_ = leanh::lean_apply_1(v_canonExpr_1604_, v___x_1608_);
    return v___x_1609_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1(
    mut v___f_1610_: *mut leanh::LeanObject,
    mut v_inst_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1612_ = leanh::lean_apply_1(v___f_1610_, v_inst_1611_);
    return v___x_1612_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3(
    mut v_toPure_1613_: *mut leanh::LeanObject,
    mut v_val_1614_: *mut leanh::LeanObject,
    mut v_toBind_1615_: *mut leanh::LeanObject,
    mut v___f_1616_: *mut leanh::LeanObject,
    mut v_____r_1617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ =
        leanh::lean_apply_2(v_toPure_1613_, leanh::lean_box(0), v_val_1614_);
    v___x_1619_ = leanh::lean_apply_4(
        v_toBind_1615_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1618_,
        v___f_1616_,
    );
    return v___x_1619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2(
    mut v_toPure_1620_: *mut leanh::LeanObject,
    mut v_inst_x27_1621_: *mut leanh::LeanObject,
    mut v_toBind_1622_: *mut leanh::LeanObject,
    mut v___f_1623_: *mut leanh::LeanObject,
    mut v___f_1624_: *mut leanh::LeanObject,
    mut v___x_1625_: *mut leanh::LeanObject,
    mut v___x_1626_: *mut leanh::LeanObject,
    mut v_inst_1627_: *mut leanh::LeanObject,
    mut v_____do__lift_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_1628_) == 0 {
        let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_1627_);
        leanh::lean_dec_ref(v___x_1626_);
        leanh::lean_dec_ref(v___x_1625_);
        leanh::lean_dec(v___f_1624_);
        v___x_1629_ =
            leanh::lean_apply_2(v_toPure_1620_, leanh::lean_box(0), v_inst_x27_1621_);
        v___x_1630_ = leanh::lean_apply_4(
            v_toBind_1622_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1629_,
            v___f_1623_,
        );
        return v___x_1630_;
    } else {
        let mut v_val_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_1623_);
        v_val_1631_ = leanh::lean_ctor_get(v_____do__lift_1628_, 0);
        leanh::lean_inc_n(v_val_1631_, 2);
        leanh::lean_dec_ref_known(v_____do__lift_1628_, 1);
        leanh::lean_inc(v_toBind_1622_);
        v___f_1632_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3
                as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1632_, 0, v_toPure_1620_);
        leanh::lean_closure_set(v___f_1632_, 1, v_val_1631_);
        leanh::lean_closure_set(v___f_1632_, 2, v_toBind_1622_);
        leanh::lean_closure_set(v___f_1632_, 3, v___f_1624_);
        v___x_1633_ = l_Lean_Name_mkStr2(v___x_1625_, v___x_1626_);
        v___x_1634_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        leanh::lean_closure_set(v___x_1634_, 0, v___x_1633_);
        leanh::lean_closure_set(v___x_1634_, 1, v_val_1631_);
        leanh::lean_closure_set(v___x_1634_, 2, v_inst_x27_1621_);
        v___x_1635_ =
            leanh::lean_apply_2(v_inst_1627_, leanh::lean_box(0), v___x_1634_);
        v___x_1636_ = leanh::lean_apply_4(
            v_toBind_1622_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1635_,
            v___f_1632_,
        );
        return v___x_1636_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
    mut v_inst_1646_: *mut leanh::LeanObject,
    mut v_inst_1647_: *mut leanh::LeanObject,
    mut v_inst_1648_: *mut leanh::LeanObject,
    mut v_u_1649_: *mut leanh::LeanObject,
    mut v_type_1650_: *mut leanh::LeanObject,
    mut v_semiringInst_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v_toPure_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instType_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1652_ = leanh::lean_ctor_get(v_inst_1647_, 0);
                leanh::lean_inc_ref(v_toApplicative_1652_);
                v_toBind_1653_ = leanh::lean_ctor_get(v_inst_1647_, 1);
                leanh::lean_inc(v_toBind_1653_);
                leanh::lean_dec_ref(v_inst_1647_);
                v_canonExpr_1654_ = leanh::lean_ctor_get(v_inst_1648_, 0);
                v_synthInstance_x3f_1655_ = leanh::lean_ctor_get(v_inst_1648_, 1);
                v_isSharedCheck_1677_ = (!leanh::lean_is_exclusive(v_inst_1648_)) as u8;
                if v_isSharedCheck_1677_ == 0 {
                    v___x_1657_ = v_inst_1648_;
                    v_isShared_1658_ = v_isSharedCheck_1677_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_synthInstance_x3f_1655_);
                    leanh::lean_inc(v_canonExpr_1654_);
                    leanh::lean_dec(v_inst_1648_);
                    v___x_1657_ = leanh::lean_box(0);
                    v_isShared_1658_ = v_isSharedCheck_1677_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1659_ = leanh::lean_ctor_get(v_toApplicative_1652_, 1);
                leanh::lean_inc(v_toPure_1659_);
                leanh::lean_dec_ref(v_toApplicative_1652_);
                v___x_1660_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__0;
                v___x_1661_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__1;
                v___x_1662_ = leanh::lean_box(0);
                if v_isShared_1658_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1657_, 1);
                    leanh::lean_ctor_set(v___x_1657_, 1, v___x_1662_);
                    leanh::lean_ctor_set(v___x_1657_, 0, v_u_1649_);
                    v___x_1664_ = v___x_1657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_u_1649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1662_);
                    v___x_1664_ = v_reuseFailAlloc_1676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref_n(v___x_1664_, 2);
                v___x_1665_ = l_Lean_mkConst(v___x_1661_, v___x_1664_);
                leanh::lean_inc_ref_n(v_type_1650_, 2);
                v_inst_x27_1666_ = l_Lean_mkAppB(v___x_1665_, v_type_1650_, v_semiringInst_1651_);
                v___x_1667_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__2;
                v___f_1668_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__0
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                leanh::lean_closure_set(v___f_1668_, 0, v___x_1667_);
                leanh::lean_closure_set(v___f_1668_, 1, v___x_1660_);
                leanh::lean_closure_set(v___f_1668_, 2, v___x_1664_);
                leanh::lean_closure_set(v___f_1668_, 3, v_type_1650_);
                leanh::lean_closure_set(v___f_1668_, 4, v_canonExpr_1654_);
                v___f_1669_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1669_, 0, v___f_1668_);
                v___x_1670_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___closed__3;
                v___x_1671_ = l_Lean_mkConst(v___x_1670_, v___x_1664_);
                v_instType_1672_ = l_Lean_Expr_app___override(v___x_1671_, v_type_1650_);
                v___x_1673_ =
                    leanh::lean_apply_1(v_synthInstance_x3f_1655_, v_instType_1672_);
                leanh::lean_inc_ref(v___f_1669_);
                leanh::lean_inc(v_toBind_1653_);
                v___f_1674_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__2
                        as *mut core::ffi::c_void,
                    9,
                    8,
                );
                leanh::lean_closure_set(v___f_1674_, 0, v_toPure_1659_);
                leanh::lean_closure_set(v___f_1674_, 1, v_inst_x27_1666_);
                leanh::lean_closure_set(v___f_1674_, 2, v_toBind_1653_);
                leanh::lean_closure_set(v___f_1674_, 3, v___f_1669_);
                leanh::lean_closure_set(v___f_1674_, 4, v___f_1669_);
                leanh::lean_closure_set(v___f_1674_, 5, v___x_1667_);
                leanh::lean_closure_set(v___f_1674_, 6, v___x_1660_);
                leanh::lean_closure_set(v___f_1674_, 7, v_inst_1646_);
                v___x_1675_ = leanh::lean_apply_4(
                    v_toBind_1653_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1673_,
                    v___f_1674_,
                );
                return v___x_1675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn(
    mut v_m_1678_: *mut leanh::LeanObject,
    mut v_inst_1679_: *mut leanh::LeanObject,
    mut v_inst_1680_: *mut leanh::LeanObject,
    mut v_inst_1681_: *mut leanh::LeanObject,
    mut v_u_1682_: *mut leanh::LeanObject,
    mut v_type_1683_: *mut leanh::LeanObject,
    mut v_semiringInst_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1685_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
        v_inst_1679_,
        v_inst_1680_,
        v_inst_1681_,
        v_u_1682_,
        v_type_1683_,
        v_semiringInst_1684_,
    );
    return v___x_1685_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0(
    mut v_addFn_1686_: *mut leanh::LeanObject,
    mut v_s_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v_unused_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1688_ = leanh::lean_ctor_get(v_s_1687_, 0);
                v_type_1689_ = leanh::lean_ctor_get(v_s_1687_, 1);
                v_u_1690_ = leanh::lean_ctor_get(v_s_1687_, 2);
                v_ringInst_1691_ = leanh::lean_ctor_get(v_s_1687_, 3);
                v_semiringInst_1692_ = leanh::lean_ctor_get(v_s_1687_, 4);
                v_charInst_x3f_1693_ = leanh::lean_ctor_get(v_s_1687_, 5);
                v_mulFn_x3f_1694_ = leanh::lean_ctor_get(v_s_1687_, 7);
                v_subFn_x3f_1695_ = leanh::lean_ctor_get(v_s_1687_, 8);
                v_negFn_x3f_1696_ = leanh::lean_ctor_get(v_s_1687_, 9);
                v_powFn_x3f_1697_ = leanh::lean_ctor_get(v_s_1687_, 10);
                v_intCastFn_x3f_1698_ = leanh::lean_ctor_get(v_s_1687_, 11);
                v_natCastFn_x3f_1699_ = leanh::lean_ctor_get(v_s_1687_, 12);
                v_one_x3f_1700_ = leanh::lean_ctor_get(v_s_1687_, 13);
                v_vars_1701_ = leanh::lean_ctor_get(v_s_1687_, 14);
                v_varMap_1702_ = leanh::lean_ctor_get(v_s_1687_, 15);
                v_denote_1703_ = leanh::lean_ctor_get(v_s_1687_, 16);
                v_isSharedCheck_1711_ = (!leanh::lean_is_exclusive(v_s_1687_)) as u8;
                if v_isSharedCheck_1711_ == 0 {
                    v_unused_1712_ = leanh::lean_ctor_get(v_s_1687_, 6);
                    leanh::lean_dec(v_unused_1712_);
                    v___x_1705_ = v_s_1687_;
                    v_isShared_1706_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_1703_);
                    leanh::lean_inc(v_varMap_1702_);
                    leanh::lean_inc(v_vars_1701_);
                    leanh::lean_inc(v_one_x3f_1700_);
                    leanh::lean_inc(v_natCastFn_x3f_1699_);
                    leanh::lean_inc(v_intCastFn_x3f_1698_);
                    leanh::lean_inc(v_powFn_x3f_1697_);
                    leanh::lean_inc(v_negFn_x3f_1696_);
                    leanh::lean_inc(v_subFn_x3f_1695_);
                    leanh::lean_inc(v_mulFn_x3f_1694_);
                    leanh::lean_inc(v_charInst_x3f_1693_);
                    leanh::lean_inc(v_semiringInst_1692_);
                    leanh::lean_inc(v_ringInst_1691_);
                    leanh::lean_inc(v_u_1690_);
                    leanh::lean_inc(v_type_1689_);
                    leanh::lean_inc(v_id_1688_);
                    leanh::lean_dec(v_s_1687_);
                    v___x_1705_ = leanh::lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1711_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1707_, 0, v_addFn_1686_);
                if v_isShared_1706_ == 0 {
                    leanh::lean_ctor_set(v___x_1705_, 6, v___x_1707_);
                    v___x_1709_ = v___x_1705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_id_1688_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_type_1689_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_u_1690_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_ringInst_1691_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_semiringInst_1692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 5, v_charInst_x3f_1693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 6, v___x_1707_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 7, v_mulFn_x3f_1694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 8, v_subFn_x3f_1695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 9, v_negFn_x3f_1696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 10, v_powFn_x3f_1697_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 11, v_intCastFn_x3f_1698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 12, v_natCastFn_x3f_1699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 13, v_one_x3f_1700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 14, v_vars_1701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 15, v_varMap_1702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 16, v_denote_1703_);
                    v___x_1709_ = v_reuseFailAlloc_1710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1(
    mut v_toPure_1713_: *mut leanh::LeanObject,
    mut v_addFn_1714_: *mut leanh::LeanObject,
    mut v_____r_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ =
        leanh::lean_apply_2(v_toPure_1713_, leanh::lean_box(0), v_addFn_1714_);
    return v___x_1716_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2(
    mut v_toPure_1717_: *mut leanh::LeanObject,
    mut v_modifyRing_1718_: *mut leanh::LeanObject,
    mut v_toBind_1719_: *mut leanh::LeanObject,
    mut v_addFn_1720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_addFn_1720_);
    v___f_1721_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1721_, 0, v_addFn_1720_);
    v___f_1722_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1722_, 0, v_toPure_1717_);
    leanh::lean_closure_set(v___f_1722_, 1, v_addFn_1720_);
    v___x_1723_ = leanh::lean_apply_1(v_modifyRing_1718_, v___f_1721_);
    v___x_1724_ = leanh::lean_apply_4(
        v_toBind_1719_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1723_,
        v___f_1722_,
    );
    return v___x_1724_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3(
    mut v_toPure_1741_: *mut leanh::LeanObject,
    mut v_inst_1742_: *mut leanh::LeanObject,
    mut v_inst_1743_: *mut leanh::LeanObject,
    mut v_inst_1744_: *mut leanh::LeanObject,
    mut v_inst_1745_: *mut leanh::LeanObject,
    mut v_toBind_1746_: *mut leanh::LeanObject,
    mut v___f_1747_: *mut leanh::LeanObject,
    mut v_ring_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_addFn_x3f_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_addFn_x3f_1749_ = leanh::lean_ctor_get(v_ring_1748_, 6);
    if leanh::lean_obj_tag(v_addFn_x3f_1749_) == 1 {
        let mut v_val_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_addFn_x3f_1749_);
        leanh::lean_dec_ref(v_ring_1748_);
        leanh::lean_dec(v___f_1747_);
        leanh::lean_dec(v_toBind_1746_);
        leanh::lean_dec_ref(v_inst_1745_);
        leanh::lean_dec_ref(v_inst_1744_);
        leanh::lean_dec_ref(v_inst_1743_);
        leanh::lean_dec(v_inst_1742_);
        v_val_1750_ = leanh::lean_ctor_get(v_addFn_x3f_1749_, 0);
        leanh::lean_inc(v_val_1750_);
        leanh::lean_dec_ref_known(v_addFn_x3f_1749_, 1);
        v___x_1751_ =
            leanh::lean_apply_2(v_toPure_1741_, leanh::lean_box(0), v_val_1750_);
        return v___x_1751_;
    } else {
        let mut v_type_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1741_);
        v_type_1752_ = leanh::lean_ctor_get(v_ring_1748_, 1);
        leanh::lean_inc_ref_n(v_type_1752_, 3);
        v_u_1753_ = leanh::lean_ctor_get(v_ring_1748_, 2);
        leanh::lean_inc_n(v_u_1753_, 2);
        v_semiringInst_1754_ = leanh::lean_ctor_get(v_ring_1748_, 4);
        leanh::lean_inc_ref(v_semiringInst_1754_);
        leanh::lean_dec_ref(v_ring_1748_);
        v___x_1755_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__1;
        v___x_1756_ = leanh::lean_box(0);
        v___x_1757_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1757_, 0, v_u_1753_);
        leanh::lean_ctor_set(v___x_1757_, 1, v___x_1756_);
        leanh::lean_inc_ref(v___x_1757_);
        v___x_1758_ = l_Lean_mkConst(v___x_1755_, v___x_1757_);
        v___x_1759_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__3;
        v___x_1760_ = l_Lean_mkConst(v___x_1759_, v___x_1757_);
        v___x_1761_ = l_Lean_mkAppB(v___x_1760_, v_type_1752_, v_semiringInst_1754_);
        v_expectedInst_1762_ = l_Lean_mkAppB(v___x_1758_, v_type_1752_, v___x_1761_);
        v___x_1763_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__5;
        v___x_1764_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3___closed__7;
        v___x_1765_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
            v_inst_1742_,
            v_inst_1743_,
            v_inst_1744_,
            v_inst_1745_,
            v_type_1752_,
            v_u_1753_,
            v___x_1763_,
            v___x_1764_,
            v_expectedInst_1762_,
        );
        v___x_1766_ = leanh::lean_apply_4(
            v_toBind_1746_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1765_,
            v___f_1747_,
        );
        return v___x_1766_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
    mut v_inst_1767_: *mut leanh::LeanObject,
    mut v_inst_1768_: *mut leanh::LeanObject,
    mut v_inst_1769_: *mut leanh::LeanObject,
    mut v_inst_1770_: *mut leanh::LeanObject,
    mut v_inst_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1772_ = leanh::lean_ctor_get(v_inst_1769_, 0);
    v_toBind_1773_ = leanh::lean_ctor_get(v_inst_1769_, 1);
    leanh::lean_inc_n(v_toBind_1773_, 3);
    v_getRing_1774_ = leanh::lean_ctor_get(v_inst_1771_, 0);
    leanh::lean_inc(v_getRing_1774_);
    v_modifyRing_1775_ = leanh::lean_ctor_get(v_inst_1771_, 1);
    leanh::lean_inc(v_modifyRing_1775_);
    leanh::lean_dec_ref(v_inst_1771_);
    v_toPure_1776_ = leanh::lean_ctor_get(v_toApplicative_1772_, 1);
    leanh::lean_inc_n(v_toPure_1776_, 2);
    v___f_1777_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1777_, 0, v_toPure_1776_);
    leanh::lean_closure_set(v___f_1777_, 1, v_modifyRing_1775_);
    leanh::lean_closure_set(v___f_1777_, 2, v_toBind_1773_);
    v___f_1778_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1778_, 0, v_toPure_1776_);
    leanh::lean_closure_set(v___f_1778_, 1, v_inst_1767_);
    leanh::lean_closure_set(v___f_1778_, 2, v_inst_1768_);
    leanh::lean_closure_set(v___f_1778_, 3, v_inst_1769_);
    leanh::lean_closure_set(v___f_1778_, 4, v_inst_1770_);
    leanh::lean_closure_set(v___f_1778_, 5, v_toBind_1773_);
    leanh::lean_closure_set(v___f_1778_, 6, v___f_1777_);
    v___x_1779_ = leanh::lean_apply_4(
        v_toBind_1773_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_1774_,
        v___f_1778_,
    );
    return v___x_1779_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getAddFn(
    mut v_m_1780_: *mut leanh::LeanObject,
    mut v_inst_1781_: *mut leanh::LeanObject,
    mut v_inst_1782_: *mut leanh::LeanObject,
    mut v_inst_1783_: *mut leanh::LeanObject,
    mut v_inst_1784_: *mut leanh::LeanObject,
    mut v_inst_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = l_Lean_Meta_Grind_Arith_CommRing_getAddFn___redArg(
        v_inst_1781_,
        v_inst_1782_,
        v_inst_1783_,
        v_inst_1784_,
        v_inst_1785_,
    );
    return v___x_1786_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0(
    mut v_subFn_1787_: *mut leanh::LeanObject,
    mut v_s_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1807_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v_unused_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1789_ = leanh::lean_ctor_get(v_s_1788_, 0);
                v_type_1790_ = leanh::lean_ctor_get(v_s_1788_, 1);
                v_u_1791_ = leanh::lean_ctor_get(v_s_1788_, 2);
                v_ringInst_1792_ = leanh::lean_ctor_get(v_s_1788_, 3);
                v_semiringInst_1793_ = leanh::lean_ctor_get(v_s_1788_, 4);
                v_charInst_x3f_1794_ = leanh::lean_ctor_get(v_s_1788_, 5);
                v_addFn_x3f_1795_ = leanh::lean_ctor_get(v_s_1788_, 6);
                v_mulFn_x3f_1796_ = leanh::lean_ctor_get(v_s_1788_, 7);
                v_negFn_x3f_1797_ = leanh::lean_ctor_get(v_s_1788_, 9);
                v_powFn_x3f_1798_ = leanh::lean_ctor_get(v_s_1788_, 10);
                v_intCastFn_x3f_1799_ = leanh::lean_ctor_get(v_s_1788_, 11);
                v_natCastFn_x3f_1800_ = leanh::lean_ctor_get(v_s_1788_, 12);
                v_one_x3f_1801_ = leanh::lean_ctor_get(v_s_1788_, 13);
                v_vars_1802_ = leanh::lean_ctor_get(v_s_1788_, 14);
                v_varMap_1803_ = leanh::lean_ctor_get(v_s_1788_, 15);
                v_denote_1804_ = leanh::lean_ctor_get(v_s_1788_, 16);
                v_isSharedCheck_1812_ = (!leanh::lean_is_exclusive(v_s_1788_)) as u8;
                if v_isSharedCheck_1812_ == 0 {
                    v_unused_1813_ = leanh::lean_ctor_get(v_s_1788_, 8);
                    leanh::lean_dec(v_unused_1813_);
                    v___x_1806_ = v_s_1788_;
                    v_isShared_1807_ = v_isSharedCheck_1812_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_1804_);
                    leanh::lean_inc(v_varMap_1803_);
                    leanh::lean_inc(v_vars_1802_);
                    leanh::lean_inc(v_one_x3f_1801_);
                    leanh::lean_inc(v_natCastFn_x3f_1800_);
                    leanh::lean_inc(v_intCastFn_x3f_1799_);
                    leanh::lean_inc(v_powFn_x3f_1798_);
                    leanh::lean_inc(v_negFn_x3f_1797_);
                    leanh::lean_inc(v_mulFn_x3f_1796_);
                    leanh::lean_inc(v_addFn_x3f_1795_);
                    leanh::lean_inc(v_charInst_x3f_1794_);
                    leanh::lean_inc(v_semiringInst_1793_);
                    leanh::lean_inc(v_ringInst_1792_);
                    leanh::lean_inc(v_u_1791_);
                    leanh::lean_inc(v_type_1790_);
                    leanh::lean_inc(v_id_1789_);
                    leanh::lean_dec(v_s_1788_);
                    v___x_1806_ = leanh::lean_box(0);
                    v_isShared_1807_ = v_isSharedCheck_1812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1808_, 0, v_subFn_1787_);
                if v_isShared_1807_ == 0 {
                    leanh::lean_ctor_set(v___x_1806_, 8, v___x_1808_);
                    v___x_1810_ = v___x_1806_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_id_1789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_type_1790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_u_1791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_ringInst_1792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 4, v_semiringInst_1793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 5, v_charInst_x3f_1794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 6, v_addFn_x3f_1795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 7, v_mulFn_x3f_1796_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 8, v___x_1808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 9, v_negFn_x3f_1797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 10, v_powFn_x3f_1798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 11, v_intCastFn_x3f_1799_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 12, v_natCastFn_x3f_1800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 13, v_one_x3f_1801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 14, v_vars_1802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 15, v_varMap_1803_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1811_, 16, v_denote_1804_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1(
    mut v_toPure_1814_: *mut leanh::LeanObject,
    mut v_subFn_1815_: *mut leanh::LeanObject,
    mut v_____r_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ =
        leanh::lean_apply_2(v_toPure_1814_, leanh::lean_box(0), v_subFn_1815_);
    return v___x_1817_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2(
    mut v_toPure_1818_: *mut leanh::LeanObject,
    mut v_modifyRing_1819_: *mut leanh::LeanObject,
    mut v_toBind_1820_: *mut leanh::LeanObject,
    mut v_subFn_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_subFn_1821_);
    v___f_1822_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1822_, 0, v_subFn_1821_);
    v___f_1823_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1823_, 0, v_toPure_1818_);
    leanh::lean_closure_set(v___f_1823_, 1, v_subFn_1821_);
    v___x_1824_ = leanh::lean_apply_1(v_modifyRing_1819_, v___f_1822_);
    v___x_1825_ = leanh::lean_apply_4(
        v_toBind_1820_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1824_,
        v___f_1823_,
    );
    return v___x_1825_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3(
    mut v_toPure_1843_: *mut leanh::LeanObject,
    mut v_inst_1844_: *mut leanh::LeanObject,
    mut v_inst_1845_: *mut leanh::LeanObject,
    mut v_inst_1846_: *mut leanh::LeanObject,
    mut v_inst_1847_: *mut leanh::LeanObject,
    mut v_toBind_1848_: *mut leanh::LeanObject,
    mut v___f_1849_: *mut leanh::LeanObject,
    mut v_ring_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_subFn_x3f_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_subFn_x3f_1851_ = leanh::lean_ctor_get(v_ring_1850_, 8);
    if leanh::lean_obj_tag(v_subFn_x3f_1851_) == 1 {
        let mut v_val_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_subFn_x3f_1851_);
        leanh::lean_dec_ref(v_ring_1850_);
        leanh::lean_dec(v___f_1849_);
        leanh::lean_dec(v_toBind_1848_);
        leanh::lean_dec_ref(v_inst_1847_);
        leanh::lean_dec_ref(v_inst_1846_);
        leanh::lean_dec_ref(v_inst_1845_);
        leanh::lean_dec(v_inst_1844_);
        v_val_1852_ = leanh::lean_ctor_get(v_subFn_x3f_1851_, 0);
        leanh::lean_inc(v_val_1852_);
        leanh::lean_dec_ref_known(v_subFn_x3f_1851_, 1);
        v___x_1853_ =
            leanh::lean_apply_2(v_toPure_1843_, leanh::lean_box(0), v_val_1852_);
        return v___x_1853_;
    } else {
        let mut v_type_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ringInst_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1843_);
        v_type_1854_ = leanh::lean_ctor_get(v_ring_1850_, 1);
        leanh::lean_inc_ref_n(v_type_1854_, 3);
        v_u_1855_ = leanh::lean_ctor_get(v_ring_1850_, 2);
        leanh::lean_inc_n(v_u_1855_, 2);
        v_ringInst_1856_ = leanh::lean_ctor_get(v_ring_1850_, 3);
        leanh::lean_inc_ref(v_ringInst_1856_);
        leanh::lean_dec_ref(v_ring_1850_);
        v___x_1857_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__1;
        v___x_1858_ = leanh::lean_box(0);
        v___x_1859_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1859_, 0, v_u_1855_);
        leanh::lean_ctor_set(v___x_1859_, 1, v___x_1858_);
        leanh::lean_inc_ref(v___x_1859_);
        v___x_1860_ = l_Lean_mkConst(v___x_1857_, v___x_1859_);
        v___x_1861_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__4;
        v___x_1862_ = l_Lean_mkConst(v___x_1861_, v___x_1859_);
        v___x_1863_ = l_Lean_mkAppB(v___x_1862_, v_type_1854_, v_ringInst_1856_);
        v_expectedInst_1864_ = l_Lean_mkAppB(v___x_1860_, v_type_1854_, v___x_1863_);
        v___x_1865_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__6;
        v___x_1866_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3___closed__8;
        v___x_1867_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
            v_inst_1844_,
            v_inst_1845_,
            v_inst_1846_,
            v_inst_1847_,
            v_type_1854_,
            v_u_1855_,
            v___x_1865_,
            v___x_1866_,
            v_expectedInst_1864_,
        );
        v___x_1868_ = leanh::lean_apply_4(
            v_toBind_1848_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1867_,
            v___f_1849_,
        );
        return v___x_1868_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(
    mut v_inst_1869_: *mut leanh::LeanObject,
    mut v_inst_1870_: *mut leanh::LeanObject,
    mut v_inst_1871_: *mut leanh::LeanObject,
    mut v_inst_1872_: *mut leanh::LeanObject,
    mut v_inst_1873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1874_ = leanh::lean_ctor_get(v_inst_1871_, 0);
    v_toBind_1875_ = leanh::lean_ctor_get(v_inst_1871_, 1);
    leanh::lean_inc_n(v_toBind_1875_, 3);
    v_getRing_1876_ = leanh::lean_ctor_get(v_inst_1873_, 0);
    leanh::lean_inc(v_getRing_1876_);
    v_modifyRing_1877_ = leanh::lean_ctor_get(v_inst_1873_, 1);
    leanh::lean_inc(v_modifyRing_1877_);
    leanh::lean_dec_ref(v_inst_1873_);
    v_toPure_1878_ = leanh::lean_ctor_get(v_toApplicative_1874_, 1);
    leanh::lean_inc_n(v_toPure_1878_, 2);
    v___f_1879_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1879_, 0, v_toPure_1878_);
    leanh::lean_closure_set(v___f_1879_, 1, v_modifyRing_1877_);
    leanh::lean_closure_set(v___f_1879_, 2, v_toBind_1875_);
    v___f_1880_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1880_, 0, v_toPure_1878_);
    leanh::lean_closure_set(v___f_1880_, 1, v_inst_1869_);
    leanh::lean_closure_set(v___f_1880_, 2, v_inst_1870_);
    leanh::lean_closure_set(v___f_1880_, 3, v_inst_1871_);
    leanh::lean_closure_set(v___f_1880_, 4, v_inst_1872_);
    leanh::lean_closure_set(v___f_1880_, 5, v_toBind_1875_);
    leanh::lean_closure_set(v___f_1880_, 6, v___f_1879_);
    v___x_1881_ = leanh::lean_apply_4(
        v_toBind_1875_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_1876_,
        v___f_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getSubFn(
    mut v_m_1882_: *mut leanh::LeanObject,
    mut v_inst_1883_: *mut leanh::LeanObject,
    mut v_inst_1884_: *mut leanh::LeanObject,
    mut v_inst_1885_: *mut leanh::LeanObject,
    mut v_inst_1886_: *mut leanh::LeanObject,
    mut v_inst_1887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_Meta_Grind_Arith_CommRing_getSubFn___redArg(
        v_inst_1883_,
        v_inst_1884_,
        v_inst_1885_,
        v_inst_1886_,
        v_inst_1887_,
    );
    return v___x_1888_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0(
    mut v_mulFn_1889_: *mut leanh::LeanObject,
    mut v_s_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1914_: u8 = 0;
    let mut v_unused_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1891_ = leanh::lean_ctor_get(v_s_1890_, 0);
                v_type_1892_ = leanh::lean_ctor_get(v_s_1890_, 1);
                v_u_1893_ = leanh::lean_ctor_get(v_s_1890_, 2);
                v_ringInst_1894_ = leanh::lean_ctor_get(v_s_1890_, 3);
                v_semiringInst_1895_ = leanh::lean_ctor_get(v_s_1890_, 4);
                v_charInst_x3f_1896_ = leanh::lean_ctor_get(v_s_1890_, 5);
                v_addFn_x3f_1897_ = leanh::lean_ctor_get(v_s_1890_, 6);
                v_subFn_x3f_1898_ = leanh::lean_ctor_get(v_s_1890_, 8);
                v_negFn_x3f_1899_ = leanh::lean_ctor_get(v_s_1890_, 9);
                v_powFn_x3f_1900_ = leanh::lean_ctor_get(v_s_1890_, 10);
                v_intCastFn_x3f_1901_ = leanh::lean_ctor_get(v_s_1890_, 11);
                v_natCastFn_x3f_1902_ = leanh::lean_ctor_get(v_s_1890_, 12);
                v_one_x3f_1903_ = leanh::lean_ctor_get(v_s_1890_, 13);
                v_vars_1904_ = leanh::lean_ctor_get(v_s_1890_, 14);
                v_varMap_1905_ = leanh::lean_ctor_get(v_s_1890_, 15);
                v_denote_1906_ = leanh::lean_ctor_get(v_s_1890_, 16);
                v_isSharedCheck_1914_ = (!leanh::lean_is_exclusive(v_s_1890_)) as u8;
                if v_isSharedCheck_1914_ == 0 {
                    v_unused_1915_ = leanh::lean_ctor_get(v_s_1890_, 7);
                    leanh::lean_dec(v_unused_1915_);
                    v___x_1908_ = v_s_1890_;
                    v_isShared_1909_ = v_isSharedCheck_1914_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_1906_);
                    leanh::lean_inc(v_varMap_1905_);
                    leanh::lean_inc(v_vars_1904_);
                    leanh::lean_inc(v_one_x3f_1903_);
                    leanh::lean_inc(v_natCastFn_x3f_1902_);
                    leanh::lean_inc(v_intCastFn_x3f_1901_);
                    leanh::lean_inc(v_powFn_x3f_1900_);
                    leanh::lean_inc(v_negFn_x3f_1899_);
                    leanh::lean_inc(v_subFn_x3f_1898_);
                    leanh::lean_inc(v_addFn_x3f_1897_);
                    leanh::lean_inc(v_charInst_x3f_1896_);
                    leanh::lean_inc(v_semiringInst_1895_);
                    leanh::lean_inc(v_ringInst_1894_);
                    leanh::lean_inc(v_u_1893_);
                    leanh::lean_inc(v_type_1892_);
                    leanh::lean_inc(v_id_1891_);
                    leanh::lean_dec(v_s_1890_);
                    v___x_1908_ = leanh::lean_box(0);
                    v_isShared_1909_ = v_isSharedCheck_1914_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1910_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1910_, 0, v_mulFn_1889_);
                if v_isShared_1909_ == 0 {
                    leanh::lean_ctor_set(v___x_1908_, 7, v___x_1910_);
                    v___x_1912_ = v___x_1908_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_id_1891_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_type_1892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_u_1893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_ringInst_1894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_semiringInst_1895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_charInst_x3f_1896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 6, v_addFn_x3f_1897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 7, v___x_1910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 8, v_subFn_x3f_1898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 9, v_negFn_x3f_1899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 10, v_powFn_x3f_1900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 11, v_intCastFn_x3f_1901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 12, v_natCastFn_x3f_1902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 13, v_one_x3f_1903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 14, v_vars_1904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 15, v_varMap_1905_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 16, v_denote_1906_);
                    v___x_1912_ = v_reuseFailAlloc_1913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1(
    mut v_toPure_1916_: *mut leanh::LeanObject,
    mut v_mulFn_1917_: *mut leanh::LeanObject,
    mut v_____r_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ =
        leanh::lean_apply_2(v_toPure_1916_, leanh::lean_box(0), v_mulFn_1917_);
    return v___x_1919_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2(
    mut v_toPure_1920_: *mut leanh::LeanObject,
    mut v_modifyRing_1921_: *mut leanh::LeanObject,
    mut v_toBind_1922_: *mut leanh::LeanObject,
    mut v_mulFn_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_mulFn_1923_);
    v___f_1924_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1924_, 0, v_mulFn_1923_);
    v___f_1925_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1925_, 0, v_toPure_1920_);
    leanh::lean_closure_set(v___f_1925_, 1, v_mulFn_1923_);
    v___x_1926_ = leanh::lean_apply_1(v_modifyRing_1921_, v___f_1924_);
    v___x_1927_ = leanh::lean_apply_4(
        v_toBind_1922_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1926_,
        v___f_1925_,
    );
    return v___x_1927_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3(
    mut v_toPure_1944_: *mut leanh::LeanObject,
    mut v_inst_1945_: *mut leanh::LeanObject,
    mut v_inst_1946_: *mut leanh::LeanObject,
    mut v_inst_1947_: *mut leanh::LeanObject,
    mut v_inst_1948_: *mut leanh::LeanObject,
    mut v_toBind_1949_: *mut leanh::LeanObject,
    mut v___f_1950_: *mut leanh::LeanObject,
    mut v_ring_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mulFn_x3f_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mulFn_x3f_1952_ = leanh::lean_ctor_get(v_ring_1951_, 7);
    if leanh::lean_obj_tag(v_mulFn_x3f_1952_) == 1 {
        let mut v_val_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_mulFn_x3f_1952_);
        leanh::lean_dec_ref(v_ring_1951_);
        leanh::lean_dec(v___f_1950_);
        leanh::lean_dec(v_toBind_1949_);
        leanh::lean_dec_ref(v_inst_1948_);
        leanh::lean_dec_ref(v_inst_1947_);
        leanh::lean_dec_ref(v_inst_1946_);
        leanh::lean_dec(v_inst_1945_);
        v_val_1953_ = leanh::lean_ctor_get(v_mulFn_x3f_1952_, 0);
        leanh::lean_inc(v_val_1953_);
        leanh::lean_dec_ref_known(v_mulFn_x3f_1952_, 1);
        v___x_1954_ =
            leanh::lean_apply_2(v_toPure_1944_, leanh::lean_box(0), v_val_1953_);
        return v___x_1954_;
    } else {
        let mut v_type_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_1944_);
        v_type_1955_ = leanh::lean_ctor_get(v_ring_1951_, 1);
        leanh::lean_inc_ref_n(v_type_1955_, 3);
        v_u_1956_ = leanh::lean_ctor_get(v_ring_1951_, 2);
        leanh::lean_inc_n(v_u_1956_, 2);
        v_semiringInst_1957_ = leanh::lean_ctor_get(v_ring_1951_, 4);
        leanh::lean_inc_ref(v_semiringInst_1957_);
        leanh::lean_dec_ref(v_ring_1951_);
        v___x_1958_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__1;
        v___x_1959_ = leanh::lean_box(0);
        v___x_1960_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1960_, 0, v_u_1956_);
        leanh::lean_ctor_set(v___x_1960_, 1, v___x_1959_);
        leanh::lean_inc_ref(v___x_1960_);
        v___x_1961_ = l_Lean_mkConst(v___x_1958_, v___x_1960_);
        v___x_1962_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__3;
        v___x_1963_ = l_Lean_mkConst(v___x_1962_, v___x_1960_);
        v___x_1964_ = l_Lean_mkAppB(v___x_1963_, v_type_1955_, v_semiringInst_1957_);
        v_expectedInst_1965_ = l_Lean_mkAppB(v___x_1961_, v_type_1955_, v___x_1964_);
        v___x_1966_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__5;
        v___x_1967_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3___closed__7;
        v___x_1968_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___redArg(
            v_inst_1945_,
            v_inst_1946_,
            v_inst_1947_,
            v_inst_1948_,
            v_type_1955_,
            v_u_1956_,
            v___x_1966_,
            v___x_1967_,
            v_expectedInst_1965_,
        );
        v___x_1969_ = leanh::lean_apply_4(
            v_toBind_1949_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1968_,
            v___f_1950_,
        );
        return v___x_1969_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
    mut v_inst_1970_: *mut leanh::LeanObject,
    mut v_inst_1971_: *mut leanh::LeanObject,
    mut v_inst_1972_: *mut leanh::LeanObject,
    mut v_inst_1973_: *mut leanh::LeanObject,
    mut v_inst_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1975_ = leanh::lean_ctor_get(v_inst_1972_, 0);
    v_toBind_1976_ = leanh::lean_ctor_get(v_inst_1972_, 1);
    leanh::lean_inc_n(v_toBind_1976_, 3);
    v_getRing_1977_ = leanh::lean_ctor_get(v_inst_1974_, 0);
    leanh::lean_inc(v_getRing_1977_);
    v_modifyRing_1978_ = leanh::lean_ctor_get(v_inst_1974_, 1);
    leanh::lean_inc(v_modifyRing_1978_);
    leanh::lean_dec_ref(v_inst_1974_);
    v_toPure_1979_ = leanh::lean_ctor_get(v_toApplicative_1975_, 1);
    leanh::lean_inc_n(v_toPure_1979_, 2);
    v___f_1980_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1980_, 0, v_toPure_1979_);
    leanh::lean_closure_set(v___f_1980_, 1, v_modifyRing_1978_);
    leanh::lean_closure_set(v___f_1980_, 2, v_toBind_1976_);
    v___f_1981_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_1981_, 0, v_toPure_1979_);
    leanh::lean_closure_set(v___f_1981_, 1, v_inst_1970_);
    leanh::lean_closure_set(v___f_1981_, 2, v_inst_1971_);
    leanh::lean_closure_set(v___f_1981_, 3, v_inst_1972_);
    leanh::lean_closure_set(v___f_1981_, 4, v_inst_1973_);
    leanh::lean_closure_set(v___f_1981_, 5, v_toBind_1976_);
    leanh::lean_closure_set(v___f_1981_, 6, v___f_1980_);
    v___x_1982_ = leanh::lean_apply_4(
        v_toBind_1976_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_1977_,
        v___f_1981_,
    );
    return v___x_1982_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn(
    mut v_m_1983_: *mut leanh::LeanObject,
    mut v_inst_1984_: *mut leanh::LeanObject,
    mut v_inst_1985_: *mut leanh::LeanObject,
    mut v_inst_1986_: *mut leanh::LeanObject,
    mut v_inst_1987_: *mut leanh::LeanObject,
    mut v_inst_1988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1989_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___redArg(
        v_inst_1984_,
        v_inst_1985_,
        v_inst_1986_,
        v_inst_1987_,
        v_inst_1988_,
    );
    return v___x_1989_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0(
    mut v_negFn_1990_: *mut leanh::LeanObject,
    mut v_s_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2015_: u8 = 0;
    let mut v_unused_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1992_ = leanh::lean_ctor_get(v_s_1991_, 0);
                v_type_1993_ = leanh::lean_ctor_get(v_s_1991_, 1);
                v_u_1994_ = leanh::lean_ctor_get(v_s_1991_, 2);
                v_ringInst_1995_ = leanh::lean_ctor_get(v_s_1991_, 3);
                v_semiringInst_1996_ = leanh::lean_ctor_get(v_s_1991_, 4);
                v_charInst_x3f_1997_ = leanh::lean_ctor_get(v_s_1991_, 5);
                v_addFn_x3f_1998_ = leanh::lean_ctor_get(v_s_1991_, 6);
                v_mulFn_x3f_1999_ = leanh::lean_ctor_get(v_s_1991_, 7);
                v_subFn_x3f_2000_ = leanh::lean_ctor_get(v_s_1991_, 8);
                v_powFn_x3f_2001_ = leanh::lean_ctor_get(v_s_1991_, 10);
                v_intCastFn_x3f_2002_ = leanh::lean_ctor_get(v_s_1991_, 11);
                v_natCastFn_x3f_2003_ = leanh::lean_ctor_get(v_s_1991_, 12);
                v_one_x3f_2004_ = leanh::lean_ctor_get(v_s_1991_, 13);
                v_vars_2005_ = leanh::lean_ctor_get(v_s_1991_, 14);
                v_varMap_2006_ = leanh::lean_ctor_get(v_s_1991_, 15);
                v_denote_2007_ = leanh::lean_ctor_get(v_s_1991_, 16);
                v_isSharedCheck_2015_ = (!leanh::lean_is_exclusive(v_s_1991_)) as u8;
                if v_isSharedCheck_2015_ == 0 {
                    v_unused_2016_ = leanh::lean_ctor_get(v_s_1991_, 9);
                    leanh::lean_dec(v_unused_2016_);
                    v___x_2009_ = v_s_1991_;
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_2007_);
                    leanh::lean_inc(v_varMap_2006_);
                    leanh::lean_inc(v_vars_2005_);
                    leanh::lean_inc(v_one_x3f_2004_);
                    leanh::lean_inc(v_natCastFn_x3f_2003_);
                    leanh::lean_inc(v_intCastFn_x3f_2002_);
                    leanh::lean_inc(v_powFn_x3f_2001_);
                    leanh::lean_inc(v_subFn_x3f_2000_);
                    leanh::lean_inc(v_mulFn_x3f_1999_);
                    leanh::lean_inc(v_addFn_x3f_1998_);
                    leanh::lean_inc(v_charInst_x3f_1997_);
                    leanh::lean_inc(v_semiringInst_1996_);
                    leanh::lean_inc(v_ringInst_1995_);
                    leanh::lean_inc(v_u_1994_);
                    leanh::lean_inc(v_type_1993_);
                    leanh::lean_inc(v_id_1992_);
                    leanh::lean_dec(v_s_1991_);
                    v___x_2009_ = leanh::lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2011_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2011_, 0, v_negFn_1990_);
                if v_isShared_2010_ == 0 {
                    leanh::lean_ctor_set(v___x_2009_, 9, v___x_2011_);
                    v___x_2013_ = v___x_2009_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2014_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_id_1992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_type_1993_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_u_1994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_ringInst_1995_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_semiringInst_1996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_charInst_x3f_1997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_addFn_x3f_1998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_mulFn_x3f_1999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_subFn_x3f_2000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 9, v___x_2011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 10, v_powFn_x3f_2001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 11, v_intCastFn_x3f_2002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 12, v_natCastFn_x3f_2003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 13, v_one_x3f_2004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 14, v_vars_2005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 15, v_varMap_2006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2014_, 16, v_denote_2007_);
                    v___x_2013_ = v_reuseFailAlloc_2014_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1(
    mut v_toPure_2017_: *mut leanh::LeanObject,
    mut v_negFn_2018_: *mut leanh::LeanObject,
    mut v_____r_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ =
        leanh::lean_apply_2(v_toPure_2017_, leanh::lean_box(0), v_negFn_2018_);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2(
    mut v_toPure_2021_: *mut leanh::LeanObject,
    mut v_modifyRing_2022_: *mut leanh::LeanObject,
    mut v_toBind_2023_: *mut leanh::LeanObject,
    mut v_negFn_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_negFn_2024_);
    v___f_2025_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2025_, 0, v_negFn_2024_);
    v___f_2026_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2026_, 0, v_toPure_2021_);
    leanh::lean_closure_set(v___f_2026_, 1, v_negFn_2024_);
    v___x_2027_ = leanh::lean_apply_1(v_modifyRing_2022_, v___f_2025_);
    v___x_2028_ = leanh::lean_apply_4(
        v_toBind_2023_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2027_,
        v___f_2026_,
    );
    return v___x_2028_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3(
    mut v_toPure_2042_: *mut leanh::LeanObject,
    mut v_inst_2043_: *mut leanh::LeanObject,
    mut v_inst_2044_: *mut leanh::LeanObject,
    mut v_inst_2045_: *mut leanh::LeanObject,
    mut v_inst_2046_: *mut leanh::LeanObject,
    mut v_toBind_2047_: *mut leanh::LeanObject,
    mut v___f_2048_: *mut leanh::LeanObject,
    mut v_ring_2049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_negFn_x3f_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_negFn_x3f_2050_ = leanh::lean_ctor_get(v_ring_2049_, 9);
    if leanh::lean_obj_tag(v_negFn_x3f_2050_) == 1 {
        let mut v_val_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_negFn_x3f_2050_);
        leanh::lean_dec_ref(v_ring_2049_);
        leanh::lean_dec(v___f_2048_);
        leanh::lean_dec(v_toBind_2047_);
        leanh::lean_dec_ref(v_inst_2046_);
        leanh::lean_dec_ref(v_inst_2045_);
        leanh::lean_dec_ref(v_inst_2044_);
        leanh::lean_dec(v_inst_2043_);
        v_val_2051_ = leanh::lean_ctor_get(v_negFn_x3f_2050_, 0);
        leanh::lean_inc(v_val_2051_);
        leanh::lean_dec_ref_known(v_negFn_x3f_2050_, 1);
        v___x_2052_ =
            leanh::lean_apply_2(v_toPure_2042_, leanh::lean_box(0), v_val_2051_);
        return v___x_2052_;
    } else {
        let mut v_type_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ringInst_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_expectedInst_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2042_);
        v_type_2053_ = leanh::lean_ctor_get(v_ring_2049_, 1);
        leanh::lean_inc_ref_n(v_type_2053_, 2);
        v_u_2054_ = leanh::lean_ctor_get(v_ring_2049_, 2);
        leanh::lean_inc_n(v_u_2054_, 2);
        v_ringInst_2055_ = leanh::lean_ctor_get(v_ring_2049_, 3);
        leanh::lean_inc_ref(v_ringInst_2055_);
        leanh::lean_dec_ref(v_ring_2049_);
        v___x_2056_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__1;
        v___x_2057_ = leanh::lean_box(0);
        v___x_2058_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2058_, 0, v_u_2054_);
        leanh::lean_ctor_set(v___x_2058_, 1, v___x_2057_);
        v___x_2059_ = l_Lean_mkConst(v___x_2056_, v___x_2058_);
        v_expectedInst_2060_ = l_Lean_mkAppB(v___x_2059_, v_type_2053_, v_ringInst_2055_);
        v___x_2061_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__3;
        v___x_2062_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3___closed__5;
        v___x_2063_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(
            v_inst_2043_,
            v_inst_2044_,
            v_inst_2045_,
            v_inst_2046_,
            v_type_2053_,
            v_u_2054_,
            v___x_2061_,
            v___x_2062_,
            v_expectedInst_2060_,
        );
        v___x_2064_ = leanh::lean_apply_4(
            v_toBind_2047_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2063_,
            v___f_2048_,
        );
        return v___x_2064_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
    mut v_inst_2065_: *mut leanh::LeanObject,
    mut v_inst_2066_: *mut leanh::LeanObject,
    mut v_inst_2067_: *mut leanh::LeanObject,
    mut v_inst_2068_: *mut leanh::LeanObject,
    mut v_inst_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2070_ = leanh::lean_ctor_get(v_inst_2067_, 0);
    v_toBind_2071_ = leanh::lean_ctor_get(v_inst_2067_, 1);
    leanh::lean_inc_n(v_toBind_2071_, 3);
    v_getRing_2072_ = leanh::lean_ctor_get(v_inst_2069_, 0);
    leanh::lean_inc(v_getRing_2072_);
    v_modifyRing_2073_ = leanh::lean_ctor_get(v_inst_2069_, 1);
    leanh::lean_inc(v_modifyRing_2073_);
    leanh::lean_dec_ref(v_inst_2069_);
    v_toPure_2074_ = leanh::lean_ctor_get(v_toApplicative_2070_, 1);
    leanh::lean_inc_n(v_toPure_2074_, 2);
    v___f_2075_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2075_, 0, v_toPure_2074_);
    leanh::lean_closure_set(v___f_2075_, 1, v_modifyRing_2073_);
    leanh::lean_closure_set(v___f_2075_, 2, v_toBind_2071_);
    v___f_2076_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2076_, 0, v_toPure_2074_);
    leanh::lean_closure_set(v___f_2076_, 1, v_inst_2065_);
    leanh::lean_closure_set(v___f_2076_, 2, v_inst_2066_);
    leanh::lean_closure_set(v___f_2076_, 3, v_inst_2067_);
    leanh::lean_closure_set(v___f_2076_, 4, v_inst_2068_);
    leanh::lean_closure_set(v___f_2076_, 5, v_toBind_2071_);
    leanh::lean_closure_set(v___f_2076_, 6, v___f_2075_);
    v___x_2077_ = leanh::lean_apply_4(
        v_toBind_2071_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_2072_,
        v___f_2076_,
    );
    return v___x_2077_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn(
    mut v_m_2078_: *mut leanh::LeanObject,
    mut v_inst_2079_: *mut leanh::LeanObject,
    mut v_inst_2080_: *mut leanh::LeanObject,
    mut v_inst_2081_: *mut leanh::LeanObject,
    mut v_inst_2082_: *mut leanh::LeanObject,
    mut v_inst_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___redArg(
        v_inst_2079_,
        v_inst_2080_,
        v_inst_2081_,
        v_inst_2082_,
        v_inst_2083_,
    );
    return v___x_2084_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0(
    mut v_powFn_2085_: *mut leanh::LeanObject,
    mut v_s_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2105_: u8 = 0;
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_unused_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2087_ = leanh::lean_ctor_get(v_s_2086_, 0);
                v_type_2088_ = leanh::lean_ctor_get(v_s_2086_, 1);
                v_u_2089_ = leanh::lean_ctor_get(v_s_2086_, 2);
                v_ringInst_2090_ = leanh::lean_ctor_get(v_s_2086_, 3);
                v_semiringInst_2091_ = leanh::lean_ctor_get(v_s_2086_, 4);
                v_charInst_x3f_2092_ = leanh::lean_ctor_get(v_s_2086_, 5);
                v_addFn_x3f_2093_ = leanh::lean_ctor_get(v_s_2086_, 6);
                v_mulFn_x3f_2094_ = leanh::lean_ctor_get(v_s_2086_, 7);
                v_subFn_x3f_2095_ = leanh::lean_ctor_get(v_s_2086_, 8);
                v_negFn_x3f_2096_ = leanh::lean_ctor_get(v_s_2086_, 9);
                v_intCastFn_x3f_2097_ = leanh::lean_ctor_get(v_s_2086_, 11);
                v_natCastFn_x3f_2098_ = leanh::lean_ctor_get(v_s_2086_, 12);
                v_one_x3f_2099_ = leanh::lean_ctor_get(v_s_2086_, 13);
                v_vars_2100_ = leanh::lean_ctor_get(v_s_2086_, 14);
                v_varMap_2101_ = leanh::lean_ctor_get(v_s_2086_, 15);
                v_denote_2102_ = leanh::lean_ctor_get(v_s_2086_, 16);
                v_isSharedCheck_2110_ = (!leanh::lean_is_exclusive(v_s_2086_)) as u8;
                if v_isSharedCheck_2110_ == 0 {
                    v_unused_2111_ = leanh::lean_ctor_get(v_s_2086_, 10);
                    leanh::lean_dec(v_unused_2111_);
                    v___x_2104_ = v_s_2086_;
                    v_isShared_2105_ = v_isSharedCheck_2110_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_2102_);
                    leanh::lean_inc(v_varMap_2101_);
                    leanh::lean_inc(v_vars_2100_);
                    leanh::lean_inc(v_one_x3f_2099_);
                    leanh::lean_inc(v_natCastFn_x3f_2098_);
                    leanh::lean_inc(v_intCastFn_x3f_2097_);
                    leanh::lean_inc(v_negFn_x3f_2096_);
                    leanh::lean_inc(v_subFn_x3f_2095_);
                    leanh::lean_inc(v_mulFn_x3f_2094_);
                    leanh::lean_inc(v_addFn_x3f_2093_);
                    leanh::lean_inc(v_charInst_x3f_2092_);
                    leanh::lean_inc(v_semiringInst_2091_);
                    leanh::lean_inc(v_ringInst_2090_);
                    leanh::lean_inc(v_u_2089_);
                    leanh::lean_inc(v_type_2088_);
                    leanh::lean_inc(v_id_2087_);
                    leanh::lean_dec(v_s_2086_);
                    v___x_2104_ = leanh::lean_box(0);
                    v_isShared_2105_ = v_isSharedCheck_2110_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2106_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2106_, 0, v_powFn_2085_);
                if v_isShared_2105_ == 0 {
                    leanh::lean_ctor_set(v___x_2104_, 10, v___x_2106_);
                    v___x_2108_ = v___x_2104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2109_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_id_2087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_type_2088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_u_2089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 3, v_ringInst_2090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_semiringInst_2091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 5, v_charInst_x3f_2092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 6, v_addFn_x3f_2093_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 7, v_mulFn_x3f_2094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 8, v_subFn_x3f_2095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 9, v_negFn_x3f_2096_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 10, v___x_2106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 11, v_intCastFn_x3f_2097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 12, v_natCastFn_x3f_2098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 13, v_one_x3f_2099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 14, v_vars_2100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 15, v_varMap_2101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 16, v_denote_2102_);
                    v___x_2108_ = v_reuseFailAlloc_2109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1(
    mut v_toPure_2112_: *mut leanh::LeanObject,
    mut v_powFn_2113_: *mut leanh::LeanObject,
    mut v_____r_2114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ =
        leanh::lean_apply_2(v_toPure_2112_, leanh::lean_box(0), v_powFn_2113_);
    return v___x_2115_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2(
    mut v_toPure_2116_: *mut leanh::LeanObject,
    mut v_modifyRing_2117_: *mut leanh::LeanObject,
    mut v_toBind_2118_: *mut leanh::LeanObject,
    mut v_powFn_2119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_powFn_2119_);
    v___f_2120_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2120_, 0, v_powFn_2119_);
    v___f_2121_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2121_, 0, v_toPure_2116_);
    leanh::lean_closure_set(v___f_2121_, 1, v_powFn_2119_);
    v___x_2122_ = leanh::lean_apply_1(v_modifyRing_2117_, v___f_2120_);
    v___x_2123_ = leanh::lean_apply_4(
        v_toBind_2118_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2122_,
        v___f_2121_,
    );
    return v___x_2123_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3(
    mut v_toPure_2124_: *mut leanh::LeanObject,
    mut v_inst_2125_: *mut leanh::LeanObject,
    mut v_inst_2126_: *mut leanh::LeanObject,
    mut v_inst_2127_: *mut leanh::LeanObject,
    mut v_inst_2128_: *mut leanh::LeanObject,
    mut v_toBind_2129_: *mut leanh::LeanObject,
    mut v___f_2130_: *mut leanh::LeanObject,
    mut v_ring_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_powFn_x3f_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_powFn_x3f_2132_ = leanh::lean_ctor_get(v_ring_2131_, 10);
    if leanh::lean_obj_tag(v_powFn_x3f_2132_) == 1 {
        let mut v_val_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_powFn_x3f_2132_);
        leanh::lean_dec_ref(v_ring_2131_);
        leanh::lean_dec(v___f_2130_);
        leanh::lean_dec(v_toBind_2129_);
        leanh::lean_dec_ref(v_inst_2128_);
        leanh::lean_dec_ref(v_inst_2127_);
        leanh::lean_dec_ref(v_inst_2126_);
        leanh::lean_dec(v_inst_2125_);
        v_val_2133_ = leanh::lean_ctor_get(v_powFn_x3f_2132_, 0);
        leanh::lean_inc(v_val_2133_);
        leanh::lean_dec_ref_known(v_powFn_x3f_2132_, 1);
        v___x_2134_ =
            leanh::lean_apply_2(v_toPure_2124_, leanh::lean_box(0), v_val_2133_);
        return v___x_2134_;
    } else {
        let mut v_type_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2124_);
        v_type_2135_ = leanh::lean_ctor_get(v_ring_2131_, 1);
        leanh::lean_inc_ref(v_type_2135_);
        v_u_2136_ = leanh::lean_ctor_get(v_ring_2131_, 2);
        leanh::lean_inc(v_u_2136_);
        v_semiringInst_2137_ = leanh::lean_ctor_get(v_ring_2131_, 4);
        leanh::lean_inc_ref(v_semiringInst_2137_);
        leanh::lean_dec_ref(v_ring_2131_);
        v___x_2138_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___redArg(
            v_inst_2125_,
            v_inst_2126_,
            v_inst_2127_,
            v_inst_2128_,
            v_u_2136_,
            v_type_2135_,
            v_semiringInst_2137_,
        );
        v___x_2139_ = leanh::lean_apply_4(
            v_toBind_2129_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2138_,
            v___f_2130_,
        );
        return v___x_2139_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
    mut v_inst_2140_: *mut leanh::LeanObject,
    mut v_inst_2141_: *mut leanh::LeanObject,
    mut v_inst_2142_: *mut leanh::LeanObject,
    mut v_inst_2143_: *mut leanh::LeanObject,
    mut v_inst_2144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2145_ = leanh::lean_ctor_get(v_inst_2142_, 0);
    v_toBind_2146_ = leanh::lean_ctor_get(v_inst_2142_, 1);
    leanh::lean_inc_n(v_toBind_2146_, 3);
    v_getRing_2147_ = leanh::lean_ctor_get(v_inst_2144_, 0);
    leanh::lean_inc(v_getRing_2147_);
    v_modifyRing_2148_ = leanh::lean_ctor_get(v_inst_2144_, 1);
    leanh::lean_inc(v_modifyRing_2148_);
    leanh::lean_dec_ref(v_inst_2144_);
    v_toPure_2149_ = leanh::lean_ctor_get(v_toApplicative_2145_, 1);
    leanh::lean_inc_n(v_toPure_2149_, 2);
    v___f_2150_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2150_, 0, v_toPure_2149_);
    leanh::lean_closure_set(v___f_2150_, 1, v_modifyRing_2148_);
    leanh::lean_closure_set(v___f_2150_, 2, v_toBind_2146_);
    v___f_2151_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2151_, 0, v_toPure_2149_);
    leanh::lean_closure_set(v___f_2151_, 1, v_inst_2140_);
    leanh::lean_closure_set(v___f_2151_, 2, v_inst_2141_);
    leanh::lean_closure_set(v___f_2151_, 3, v_inst_2142_);
    leanh::lean_closure_set(v___f_2151_, 4, v_inst_2143_);
    leanh::lean_closure_set(v___f_2151_, 5, v_toBind_2146_);
    leanh::lean_closure_set(v___f_2151_, 6, v___f_2150_);
    v___x_2152_ = leanh::lean_apply_4(
        v_toBind_2146_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_2147_,
        v___f_2151_,
    );
    return v___x_2152_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn(
    mut v_m_2153_: *mut leanh::LeanObject,
    mut v_inst_2154_: *mut leanh::LeanObject,
    mut v_inst_2155_: *mut leanh::LeanObject,
    mut v_inst_2156_: *mut leanh::LeanObject,
    mut v_inst_2157_: *mut leanh::LeanObject,
    mut v_inst_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___redArg(
        v_inst_2154_,
        v_inst_2155_,
        v_inst_2156_,
        v_inst_2157_,
        v_inst_2158_,
    );
    return v___x_2159_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0(
    mut v_intCastFn_2160_: *mut leanh::LeanObject,
    mut v_s_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_unused_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2162_ = leanh::lean_ctor_get(v_s_2161_, 0);
                v_type_2163_ = leanh::lean_ctor_get(v_s_2161_, 1);
                v_u_2164_ = leanh::lean_ctor_get(v_s_2161_, 2);
                v_ringInst_2165_ = leanh::lean_ctor_get(v_s_2161_, 3);
                v_semiringInst_2166_ = leanh::lean_ctor_get(v_s_2161_, 4);
                v_charInst_x3f_2167_ = leanh::lean_ctor_get(v_s_2161_, 5);
                v_addFn_x3f_2168_ = leanh::lean_ctor_get(v_s_2161_, 6);
                v_mulFn_x3f_2169_ = leanh::lean_ctor_get(v_s_2161_, 7);
                v_subFn_x3f_2170_ = leanh::lean_ctor_get(v_s_2161_, 8);
                v_negFn_x3f_2171_ = leanh::lean_ctor_get(v_s_2161_, 9);
                v_powFn_x3f_2172_ = leanh::lean_ctor_get(v_s_2161_, 10);
                v_natCastFn_x3f_2173_ = leanh::lean_ctor_get(v_s_2161_, 12);
                v_one_x3f_2174_ = leanh::lean_ctor_get(v_s_2161_, 13);
                v_vars_2175_ = leanh::lean_ctor_get(v_s_2161_, 14);
                v_varMap_2176_ = leanh::lean_ctor_get(v_s_2161_, 15);
                v_denote_2177_ = leanh::lean_ctor_get(v_s_2161_, 16);
                v_isSharedCheck_2185_ = (!leanh::lean_is_exclusive(v_s_2161_)) as u8;
                if v_isSharedCheck_2185_ == 0 {
                    v_unused_2186_ = leanh::lean_ctor_get(v_s_2161_, 11);
                    leanh::lean_dec(v_unused_2186_);
                    v___x_2179_ = v_s_2161_;
                    v_isShared_2180_ = v_isSharedCheck_2185_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_2177_);
                    leanh::lean_inc(v_varMap_2176_);
                    leanh::lean_inc(v_vars_2175_);
                    leanh::lean_inc(v_one_x3f_2174_);
                    leanh::lean_inc(v_natCastFn_x3f_2173_);
                    leanh::lean_inc(v_powFn_x3f_2172_);
                    leanh::lean_inc(v_negFn_x3f_2171_);
                    leanh::lean_inc(v_subFn_x3f_2170_);
                    leanh::lean_inc(v_mulFn_x3f_2169_);
                    leanh::lean_inc(v_addFn_x3f_2168_);
                    leanh::lean_inc(v_charInst_x3f_2167_);
                    leanh::lean_inc(v_semiringInst_2166_);
                    leanh::lean_inc(v_ringInst_2165_);
                    leanh::lean_inc(v_u_2164_);
                    leanh::lean_inc(v_type_2163_);
                    leanh::lean_inc(v_id_2162_);
                    leanh::lean_dec(v_s_2161_);
                    v___x_2179_ = leanh::lean_box(0);
                    v_isShared_2180_ = v_isSharedCheck_2185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2181_, 0, v_intCastFn_2160_);
                if v_isShared_2180_ == 0 {
                    leanh::lean_ctor_set(v___x_2179_, 11, v___x_2181_);
                    v___x_2183_ = v___x_2179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_id_2162_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_type_2163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_u_2164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 3, v_ringInst_2165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 4, v_semiringInst_2166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 5, v_charInst_x3f_2167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 6, v_addFn_x3f_2168_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 7, v_mulFn_x3f_2169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 8, v_subFn_x3f_2170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 9, v_negFn_x3f_2171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 10, v_powFn_x3f_2172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 11, v___x_2181_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 12, v_natCastFn_x3f_2173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 13, v_one_x3f_2174_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 14, v_vars_2175_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 15, v_varMap_2176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 16, v_denote_2177_);
                    v___x_2183_ = v_reuseFailAlloc_2184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1(
    mut v_toPure_2187_: *mut leanh::LeanObject,
    mut v_intCastFn_2188_: *mut leanh::LeanObject,
    mut v_____r_2189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ =
        leanh::lean_apply_2(v_toPure_2187_, leanh::lean_box(0), v_intCastFn_2188_);
    return v___x_2190_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2(
    mut v_toPure_2191_: *mut leanh::LeanObject,
    mut v_modifyRing_2192_: *mut leanh::LeanObject,
    mut v_toBind_2193_: *mut leanh::LeanObject,
    mut v_intCastFn_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_intCastFn_2194_);
    v___f_2195_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2195_, 0, v_intCastFn_2194_);
    v___f_2196_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2196_, 0, v_toPure_2191_);
    leanh::lean_closure_set(v___f_2196_, 1, v_intCastFn_2194_);
    v___x_2197_ = leanh::lean_apply_1(v_modifyRing_2192_, v___f_2195_);
    v___x_2198_ = leanh::lean_apply_4(
        v_toBind_2193_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2197_,
        v___f_2196_,
    );
    return v___x_2198_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3(
    mut v___x_2199_: *mut leanh::LeanObject,
    mut v___x_2200_: *mut leanh::LeanObject,
    mut v___x_2201_: *mut leanh::LeanObject,
    mut v_type_2202_: *mut leanh::LeanObject,
    mut v_canonExpr_2203_: *mut leanh::LeanObject,
    mut v_toBind_2204_: *mut leanh::LeanObject,
    mut v___f_2205_: *mut leanh::LeanObject,
    mut v_inst_2206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ = l_Lean_Name_mkStr2(v___x_2199_, v___x_2200_);
    v___x_2208_ = l_Lean_mkConst(v___x_2207_, v___x_2201_);
    v___x_2209_ = l_Lean_mkAppB(v___x_2208_, v_type_2202_, v_inst_2206_);
    v___x_2210_ = leanh::lean_apply_1(v_canonExpr_2203_, v___x_2209_);
    v___x_2211_ = leanh::lean_apply_4(
        v_toBind_2204_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2210_,
        v___f_2205_,
    );
    return v___x_2211_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7(
    mut v_toPure_2217_: *mut leanh::LeanObject,
    mut v_inst_x27_2218_: *mut leanh::LeanObject,
    mut v_toBind_2219_: *mut leanh::LeanObject,
    mut v___f_2220_: *mut leanh::LeanObject,
    mut v___f_2221_: *mut leanh::LeanObject,
    mut v_inst_2222_: *mut leanh::LeanObject,
    mut v_____do__lift_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2223_) == 0 {
        let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_inst_2222_);
        leanh::lean_dec(v___f_2221_);
        v___x_2224_ =
            leanh::lean_apply_2(v_toPure_2217_, leanh::lean_box(0), v_inst_x27_2218_);
        v___x_2225_ = leanh::lean_apply_4(
            v_toBind_2219_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2224_,
            v___f_2220_,
        );
        return v___x_2225_;
    } else {
        let mut v_val_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2220_);
        v_val_2226_ = leanh::lean_ctor_get(v_____do__lift_2223_, 0);
        leanh::lean_inc_n(v_val_2226_, 2);
        leanh::lean_dec_ref_known(v_____do__lift_2223_, 1);
        leanh::lean_inc(v_toBind_2219_);
        v___f_2227_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__3
                as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_2227_, 0, v_toPure_2217_);
        leanh::lean_closure_set(v___f_2227_, 1, v_val_2226_);
        leanh::lean_closure_set(v___f_2227_, 2, v_toBind_2219_);
        leanh::lean_closure_set(v___f_2227_, 3, v___f_2221_);
        v___x_2228_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7___closed__2;
        v___x_2229_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_CommRing_checkInst___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        leanh::lean_closure_set(v___x_2229_, 0, v___x_2228_);
        leanh::lean_closure_set(v___x_2229_, 1, v_val_2226_);
        leanh::lean_closure_set(v___x_2229_, 2, v_inst_x27_2218_);
        v___x_2230_ =
            leanh::lean_apply_2(v_inst_2222_, leanh::lean_box(0), v___x_2229_);
        v___x_2231_ = leanh::lean_apply_4(
            v_toBind_2219_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2230_,
            v___f_2227_,
        );
        return v___x_2231_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4(
    mut v_toPure_2241_: *mut leanh::LeanObject,
    mut v_inst_2242_: *mut leanh::LeanObject,
    mut v_toBind_2243_: *mut leanh::LeanObject,
    mut v___f_2244_: *mut leanh::LeanObject,
    mut v_inst_2245_: *mut leanh::LeanObject,
    mut v_ring_2246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intCastFn_x3f_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonExpr_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthInstance_x3f_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_instType_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_intCastFn_x3f_2247_ = leanh::lean_ctor_get(v_ring_2246_, 11);
                if leanh::lean_obj_tag(v_intCastFn_x3f_2247_) == 1 {
                    leanh::lean_inc_ref(v_intCastFn_x3f_2247_);
                    leanh::lean_dec_ref(v_ring_2246_);
                    leanh::lean_dec(v_inst_2245_);
                    leanh::lean_dec(v___f_2244_);
                    leanh::lean_dec(v_toBind_2243_);
                    leanh::lean_dec_ref(v_inst_2242_);
                    v_val_2248_ = leanh::lean_ctor_get(v_intCastFn_x3f_2247_, 0);
                    leanh::lean_inc(v_val_2248_);
                    leanh::lean_dec_ref_known(v_intCastFn_x3f_2247_, 1);
                    v___x_2249_ = leanh::lean_apply_2(
                        v_toPure_2241_,
                        leanh::lean_box(0),
                        v_val_2248_,
                    );
                    return v___x_2249_;
                } else {
                    v_type_2250_ = leanh::lean_ctor_get(v_ring_2246_, 1);
                    leanh::lean_inc_ref(v_type_2250_);
                    v_u_2251_ = leanh::lean_ctor_get(v_ring_2246_, 2);
                    leanh::lean_inc(v_u_2251_);
                    v_ringInst_2252_ = leanh::lean_ctor_get(v_ring_2246_, 3);
                    leanh::lean_inc_ref(v_ringInst_2252_);
                    leanh::lean_dec_ref(v_ring_2246_);
                    v_canonExpr_2253_ = leanh::lean_ctor_get(v_inst_2242_, 0);
                    v_synthInstance_x3f_2254_ = leanh::lean_ctor_get(v_inst_2242_, 1);
                    v_isSharedCheck_2275_ = (!leanh::lean_is_exclusive(v_inst_2242_)) as u8;
                    if v_isSharedCheck_2275_ == 0 {
                        v___x_2256_ = v_inst_2242_;
                        v_isShared_2257_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_synthInstance_x3f_2254_);
                        leanh::lean_inc(v_canonExpr_2253_);
                        leanh::lean_dec(v_inst_2242_);
                        v___x_2256_ = leanh::lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2258_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__0;
                v___x_2259_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__1;
                v___x_2260_ = leanh::lean_box(0);
                if v_isShared_2257_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2256_, 1);
                    leanh::lean_ctor_set(v___x_2256_, 1, v___x_2260_);
                    leanh::lean_ctor_set(v___x_2256_, 0, v_u_2251_);
                    v___x_2262_ = v___x_2256_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_u_2251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_2260_);
                    v___x_2262_ = v_reuseFailAlloc_2274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref_n(v___x_2262_, 2);
                v___x_2263_ = l_Lean_mkConst(v___x_2259_, v___x_2262_);
                leanh::lean_inc_ref_n(v_type_2250_, 2);
                v_inst_x27_2264_ = l_Lean_mkAppB(v___x_2263_, v_type_2250_, v_ringInst_2252_);
                v___x_2265_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__2;
                leanh::lean_inc_n(v_toBind_2243_, 2);
                v___f_2266_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__3
                        as *mut core::ffi::c_void,
                    8,
                    7,
                );
                leanh::lean_closure_set(v___f_2266_, 0, v___x_2265_);
                leanh::lean_closure_set(v___f_2266_, 1, v___x_2258_);
                leanh::lean_closure_set(v___f_2266_, 2, v___x_2262_);
                leanh::lean_closure_set(v___f_2266_, 3, v_type_2250_);
                leanh::lean_closure_set(v___f_2266_, 4, v_canonExpr_2253_);
                leanh::lean_closure_set(v___f_2266_, 5, v_toBind_2243_);
                leanh::lean_closure_set(v___f_2266_, 6, v___f_2244_);
                v___f_2267_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg___lam__1
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2267_, 0, v___f_2266_);
                leanh::lean_inc_ref(v___f_2267_);
                v___f_2268_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__7
                        as *mut core::ffi::c_void,
                    7,
                    6,
                );
                leanh::lean_closure_set(v___f_2268_, 0, v_toPure_2241_);
                leanh::lean_closure_set(v___f_2268_, 1, v_inst_x27_2264_);
                leanh::lean_closure_set(v___f_2268_, 2, v_toBind_2243_);
                leanh::lean_closure_set(v___f_2268_, 3, v___f_2267_);
                leanh::lean_closure_set(v___f_2268_, 4, v___f_2267_);
                leanh::lean_closure_set(v___f_2268_, 5, v_inst_2245_);
                v___x_2269_ =
                    l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4___closed__3;
                v___x_2270_ = l_Lean_mkConst(v___x_2269_, v___x_2262_);
                v_instType_2271_ = l_Lean_Expr_app___override(v___x_2270_, v_type_2250_);
                v___x_2272_ =
                    leanh::lean_apply_1(v_synthInstance_x3f_2254_, v_instType_2271_);
                v___x_2273_ = leanh::lean_apply_4(
                    v_toBind_2243_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2272_,
                    v___f_2268_,
                );
                return v___x_2273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(
    mut v_inst_2276_: *mut leanh::LeanObject,
    mut v_inst_2277_: *mut leanh::LeanObject,
    mut v_inst_2278_: *mut leanh::LeanObject,
    mut v_inst_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2280_ = leanh::lean_ctor_get(v_inst_2277_, 0);
    leanh::lean_inc_ref(v_toApplicative_2280_);
    v_toBind_2281_ = leanh::lean_ctor_get(v_inst_2277_, 1);
    leanh::lean_inc_n(v_toBind_2281_, 3);
    leanh::lean_dec_ref(v_inst_2277_);
    v_getRing_2282_ = leanh::lean_ctor_get(v_inst_2279_, 0);
    leanh::lean_inc(v_getRing_2282_);
    v_modifyRing_2283_ = leanh::lean_ctor_get(v_inst_2279_, 1);
    leanh::lean_inc(v_modifyRing_2283_);
    leanh::lean_dec_ref(v_inst_2279_);
    v_toPure_2284_ = leanh::lean_ctor_get(v_toApplicative_2280_, 1);
    leanh::lean_inc_n(v_toPure_2284_, 2);
    leanh::lean_dec_ref(v_toApplicative_2280_);
    v___f_2285_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2285_, 0, v_toPure_2284_);
    leanh::lean_closure_set(v___f_2285_, 1, v_modifyRing_2283_);
    leanh::lean_closure_set(v___f_2285_, 2, v_toBind_2281_);
    v___f_2286_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_2286_, 0, v_toPure_2284_);
    leanh::lean_closure_set(v___f_2286_, 1, v_inst_2278_);
    leanh::lean_closure_set(v___f_2286_, 2, v_toBind_2281_);
    leanh::lean_closure_set(v___f_2286_, 3, v___f_2285_);
    leanh::lean_closure_set(v___f_2286_, 4, v_inst_2276_);
    v___x_2287_ = leanh::lean_apply_4(
        v_toBind_2281_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_2282_,
        v___f_2286_,
    );
    return v___x_2287_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn(
    mut v_m_2288_: *mut leanh::LeanObject,
    mut v_inst_2289_: *mut leanh::LeanObject,
    mut v_inst_2290_: *mut leanh::LeanObject,
    mut v_inst_2291_: *mut leanh::LeanObject,
    mut v_inst_2292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___redArg(
        v_inst_2289_,
        v_inst_2290_,
        v_inst_2291_,
        v_inst_2292_,
    );
    return v___x_2293_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0(
    mut v_natCastFn_2294_: *mut leanh::LeanObject,
    mut v_s_2295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_unused_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2296_ = leanh::lean_ctor_get(v_s_2295_, 0);
                v_type_2297_ = leanh::lean_ctor_get(v_s_2295_, 1);
                v_u_2298_ = leanh::lean_ctor_get(v_s_2295_, 2);
                v_ringInst_2299_ = leanh::lean_ctor_get(v_s_2295_, 3);
                v_semiringInst_2300_ = leanh::lean_ctor_get(v_s_2295_, 4);
                v_charInst_x3f_2301_ = leanh::lean_ctor_get(v_s_2295_, 5);
                v_addFn_x3f_2302_ = leanh::lean_ctor_get(v_s_2295_, 6);
                v_mulFn_x3f_2303_ = leanh::lean_ctor_get(v_s_2295_, 7);
                v_subFn_x3f_2304_ = leanh::lean_ctor_get(v_s_2295_, 8);
                v_negFn_x3f_2305_ = leanh::lean_ctor_get(v_s_2295_, 9);
                v_powFn_x3f_2306_ = leanh::lean_ctor_get(v_s_2295_, 10);
                v_intCastFn_x3f_2307_ = leanh::lean_ctor_get(v_s_2295_, 11);
                v_one_x3f_2308_ = leanh::lean_ctor_get(v_s_2295_, 13);
                v_vars_2309_ = leanh::lean_ctor_get(v_s_2295_, 14);
                v_varMap_2310_ = leanh::lean_ctor_get(v_s_2295_, 15);
                v_denote_2311_ = leanh::lean_ctor_get(v_s_2295_, 16);
                v_isSharedCheck_2319_ = (!leanh::lean_is_exclusive(v_s_2295_)) as u8;
                if v_isSharedCheck_2319_ == 0 {
                    v_unused_2320_ = leanh::lean_ctor_get(v_s_2295_, 12);
                    leanh::lean_dec(v_unused_2320_);
                    v___x_2313_ = v_s_2295_;
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_2311_);
                    leanh::lean_inc(v_varMap_2310_);
                    leanh::lean_inc(v_vars_2309_);
                    leanh::lean_inc(v_one_x3f_2308_);
                    leanh::lean_inc(v_intCastFn_x3f_2307_);
                    leanh::lean_inc(v_powFn_x3f_2306_);
                    leanh::lean_inc(v_negFn_x3f_2305_);
                    leanh::lean_inc(v_subFn_x3f_2304_);
                    leanh::lean_inc(v_mulFn_x3f_2303_);
                    leanh::lean_inc(v_addFn_x3f_2302_);
                    leanh::lean_inc(v_charInst_x3f_2301_);
                    leanh::lean_inc(v_semiringInst_2300_);
                    leanh::lean_inc(v_ringInst_2299_);
                    leanh::lean_inc(v_u_2298_);
                    leanh::lean_inc(v_type_2297_);
                    leanh::lean_inc(v_id_2296_);
                    leanh::lean_dec(v_s_2295_);
                    v___x_2313_ = leanh::lean_box(0);
                    v_isShared_2314_ = v_isSharedCheck_2319_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2315_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2315_, 0, v_natCastFn_2294_);
                if v_isShared_2314_ == 0 {
                    leanh::lean_ctor_set(v___x_2313_, 12, v___x_2315_);
                    v___x_2317_ = v___x_2313_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2318_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_id_2296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_type_2297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_u_2298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_ringInst_2299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_semiringInst_2300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 5, v_charInst_x3f_2301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 6, v_addFn_x3f_2302_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 7, v_mulFn_x3f_2303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 8, v_subFn_x3f_2304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 9, v_negFn_x3f_2305_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 10, v_powFn_x3f_2306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 11, v_intCastFn_x3f_2307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 12, v___x_2315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 13, v_one_x3f_2308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 14, v_vars_2309_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 15, v_varMap_2310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2318_, 16, v_denote_2311_);
                    v___x_2317_ = v_reuseFailAlloc_2318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1(
    mut v_toPure_2321_: *mut leanh::LeanObject,
    mut v_natCastFn_2322_: *mut leanh::LeanObject,
    mut v_____r_2323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2324_ =
        leanh::lean_apply_2(v_toPure_2321_, leanh::lean_box(0), v_natCastFn_2322_);
    return v___x_2324_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2(
    mut v_toPure_2325_: *mut leanh::LeanObject,
    mut v_modifyRing_2326_: *mut leanh::LeanObject,
    mut v_toBind_2327_: *mut leanh::LeanObject,
    mut v_natCastFn_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_natCastFn_2328_);
    v___f_2329_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2329_, 0, v_natCastFn_2328_);
    v___f_2330_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2330_, 0, v_toPure_2325_);
    leanh::lean_closure_set(v___f_2330_, 1, v_natCastFn_2328_);
    v___x_2331_ = leanh::lean_apply_1(v_modifyRing_2326_, v___f_2329_);
    v___x_2332_ = leanh::lean_apply_4(
        v_toBind_2327_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2331_,
        v___f_2330_,
    );
    return v___x_2332_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3(
    mut v_toPure_2333_: *mut leanh::LeanObject,
    mut v_inst_2334_: *mut leanh::LeanObject,
    mut v_inst_2335_: *mut leanh::LeanObject,
    mut v_inst_2336_: *mut leanh::LeanObject,
    mut v_toBind_2337_: *mut leanh::LeanObject,
    mut v___f_2338_: *mut leanh::LeanObject,
    mut v_ring_2339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natCastFn_x3f_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natCastFn_x3f_2340_ = leanh::lean_ctor_get(v_ring_2339_, 12);
    if leanh::lean_obj_tag(v_natCastFn_x3f_2340_) == 1 {
        let mut v_val_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_natCastFn_x3f_2340_);
        leanh::lean_dec_ref(v_ring_2339_);
        leanh::lean_dec(v___f_2338_);
        leanh::lean_dec(v_toBind_2337_);
        leanh::lean_dec_ref(v_inst_2336_);
        leanh::lean_dec_ref(v_inst_2335_);
        leanh::lean_dec(v_inst_2334_);
        v_val_2341_ = leanh::lean_ctor_get(v_natCastFn_x3f_2340_, 0);
        leanh::lean_inc(v_val_2341_);
        leanh::lean_dec_ref_known(v_natCastFn_x3f_2340_, 1);
        v___x_2342_ =
            leanh::lean_apply_2(v_toPure_2333_, leanh::lean_box(0), v_val_2341_);
        return v___x_2342_;
    } else {
        let mut v_type_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2333_);
        v_type_2343_ = leanh::lean_ctor_get(v_ring_2339_, 1);
        leanh::lean_inc_ref(v_type_2343_);
        v_u_2344_ = leanh::lean_ctor_get(v_ring_2339_, 2);
        leanh::lean_inc(v_u_2344_);
        v_semiringInst_2345_ = leanh::lean_ctor_get(v_ring_2339_, 4);
        leanh::lean_inc_ref(v_semiringInst_2345_);
        leanh::lean_dec_ref(v_ring_2339_);
        v___x_2346_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___redArg(
            v_inst_2334_,
            v_inst_2335_,
            v_inst_2336_,
            v_u_2344_,
            v_type_2343_,
            v_semiringInst_2345_,
        );
        v___x_2347_ = leanh::lean_apply_4(
            v_toBind_2337_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2346_,
            v___f_2338_,
        );
        return v___x_2347_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
    mut v_inst_2348_: *mut leanh::LeanObject,
    mut v_inst_2349_: *mut leanh::LeanObject,
    mut v_inst_2350_: *mut leanh::LeanObject,
    mut v_inst_2351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2352_ = leanh::lean_ctor_get(v_inst_2349_, 0);
    v_toBind_2353_ = leanh::lean_ctor_get(v_inst_2349_, 1);
    leanh::lean_inc_n(v_toBind_2353_, 3);
    v_getRing_2354_ = leanh::lean_ctor_get(v_inst_2351_, 0);
    leanh::lean_inc(v_getRing_2354_);
    v_modifyRing_2355_ = leanh::lean_ctor_get(v_inst_2351_, 1);
    leanh::lean_inc(v_modifyRing_2355_);
    leanh::lean_dec_ref(v_inst_2351_);
    v_toPure_2356_ = leanh::lean_ctor_get(v_toApplicative_2352_, 1);
    leanh::lean_inc_n(v_toPure_2356_, 2);
    v___f_2357_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2357_, 0, v_toPure_2356_);
    leanh::lean_closure_set(v___f_2357_, 1, v_modifyRing_2355_);
    leanh::lean_closure_set(v___f_2357_, 2, v_toBind_2353_);
    v___f_2358_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_2358_, 0, v_toPure_2356_);
    leanh::lean_closure_set(v___f_2358_, 1, v_inst_2348_);
    leanh::lean_closure_set(v___f_2358_, 2, v_inst_2349_);
    leanh::lean_closure_set(v___f_2358_, 3, v_inst_2350_);
    leanh::lean_closure_set(v___f_2358_, 4, v_toBind_2353_);
    leanh::lean_closure_set(v___f_2358_, 5, v___f_2357_);
    v___x_2359_ = leanh::lean_apply_4(
        v_toBind_2353_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_2354_,
        v___f_2358_,
    );
    return v___x_2359_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn(
    mut v_m_2360_: *mut leanh::LeanObject,
    mut v_inst_2361_: *mut leanh::LeanObject,
    mut v_inst_2362_: *mut leanh::LeanObject,
    mut v_inst_2363_: *mut leanh::LeanObject,
    mut v_inst_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2365_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___redArg(
        v_inst_2361_,
        v_inst_2362_,
        v_inst_2363_,
        v_inst_2364_,
    );
    return v___x_2365_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = leanh::lean_unsigned_to_nat(1);
    v_n_2367_ = l_Lean_mkRawNatLit(v___x_2366_);
    return v_n_2367_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(
    mut v_inst_2378_: *mut leanh::LeanObject,
    mut v_u_2379_: *mut leanh::LeanObject,
    mut v_type_2380_: *mut leanh::LeanObject,
    mut v_semiringInst_2381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonExpr_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v_n_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNatInst_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2398_: u8 = 0;
    let mut v_unused_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_canonExpr_2382_ = leanh::lean_ctor_get(v_inst_2378_, 0);
                v_isSharedCheck_2398_ = (!leanh::lean_is_exclusive(v_inst_2378_)) as u8;
                if v_isSharedCheck_2398_ == 0 {
                    v_unused_2399_ = leanh::lean_ctor_get(v_inst_2378_, 1);
                    leanh::lean_dec(v_unused_2399_);
                    v___x_2384_ = v_inst_2378_;
                    v_isShared_2385_ = v_isSharedCheck_2398_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_canonExpr_2382_);
                    leanh::lean_dec(v_inst_2378_);
                    v___x_2384_ = leanh::lean_box(0);
                    v_isShared_2385_ = v_isSharedCheck_2398_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_n_2386_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__0);
                v___x_2387_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__2;
                v___x_2388_ = leanh::lean_box(0);
                if v_isShared_2385_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2384_, 1);
                    leanh::lean_ctor_set(v___x_2384_, 1, v___x_2388_);
                    leanh::lean_ctor_set(v___x_2384_, 0, v_u_2379_);
                    v___x_2390_ = v___x_2384_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2397_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_u_2379_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2388_);
                    v___x_2390_ = v_reuseFailAlloc_2397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v___x_2390_);
                v___x_2391_ = l_Lean_mkConst(v___x_2387_, v___x_2390_);
                leanh::lean_inc_ref(v_type_2380_);
                v_ofNatInst_2392_ =
                    l_Lean_mkApp3(v___x_2391_, v_type_2380_, v_semiringInst_2381_, v_n_2386_);
                v___x_2393_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg___closed__4;
                v___x_2394_ = l_Lean_mkConst(v___x_2393_, v___x_2390_);
                v___x_2395_ =
                    l_Lean_mkApp3(v___x_2394_, v_type_2380_, v_n_2386_, v_ofNatInst_2392_);
                v___x_2396_ = leanh::lean_apply_1(v_canonExpr_2382_, v___x_2395_);
                return v___x_2396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne(
    mut v_m_2400_: *mut leanh::LeanObject,
    mut v_inst_2401_: *mut leanh::LeanObject,
    mut v_u_2402_: *mut leanh::LeanObject,
    mut v_type_2403_: *mut leanh::LeanObject,
    mut v_semiringInst_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2405_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_2401_, v_u_2402_, v_type_2403_, v_semiringInst_2404_);
    return v___x_2405_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0(
    mut v_one_2406_: *mut leanh::LeanObject,
    mut v_s_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2431_: u8 = 0;
    let mut v_unused_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_2408_ = leanh::lean_ctor_get(v_s_2407_, 0);
                v_type_2409_ = leanh::lean_ctor_get(v_s_2407_, 1);
                v_u_2410_ = leanh::lean_ctor_get(v_s_2407_, 2);
                v_ringInst_2411_ = leanh::lean_ctor_get(v_s_2407_, 3);
                v_semiringInst_2412_ = leanh::lean_ctor_get(v_s_2407_, 4);
                v_charInst_x3f_2413_ = leanh::lean_ctor_get(v_s_2407_, 5);
                v_addFn_x3f_2414_ = leanh::lean_ctor_get(v_s_2407_, 6);
                v_mulFn_x3f_2415_ = leanh::lean_ctor_get(v_s_2407_, 7);
                v_subFn_x3f_2416_ = leanh::lean_ctor_get(v_s_2407_, 8);
                v_negFn_x3f_2417_ = leanh::lean_ctor_get(v_s_2407_, 9);
                v_powFn_x3f_2418_ = leanh::lean_ctor_get(v_s_2407_, 10);
                v_intCastFn_x3f_2419_ = leanh::lean_ctor_get(v_s_2407_, 11);
                v_natCastFn_x3f_2420_ = leanh::lean_ctor_get(v_s_2407_, 12);
                v_vars_2421_ = leanh::lean_ctor_get(v_s_2407_, 14);
                v_varMap_2422_ = leanh::lean_ctor_get(v_s_2407_, 15);
                v_denote_2423_ = leanh::lean_ctor_get(v_s_2407_, 16);
                v_isSharedCheck_2431_ = (!leanh::lean_is_exclusive(v_s_2407_)) as u8;
                if v_isSharedCheck_2431_ == 0 {
                    v_unused_2432_ = leanh::lean_ctor_get(v_s_2407_, 13);
                    leanh::lean_dec(v_unused_2432_);
                    v___x_2425_ = v_s_2407_;
                    v_isShared_2426_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_denote_2423_);
                    leanh::lean_inc(v_varMap_2422_);
                    leanh::lean_inc(v_vars_2421_);
                    leanh::lean_inc(v_natCastFn_x3f_2420_);
                    leanh::lean_inc(v_intCastFn_x3f_2419_);
                    leanh::lean_inc(v_powFn_x3f_2418_);
                    leanh::lean_inc(v_negFn_x3f_2417_);
                    leanh::lean_inc(v_subFn_x3f_2416_);
                    leanh::lean_inc(v_mulFn_x3f_2415_);
                    leanh::lean_inc(v_addFn_x3f_2414_);
                    leanh::lean_inc(v_charInst_x3f_2413_);
                    leanh::lean_inc(v_semiringInst_2412_);
                    leanh::lean_inc(v_ringInst_2411_);
                    leanh::lean_inc(v_u_2410_);
                    leanh::lean_inc(v_type_2409_);
                    leanh::lean_inc(v_id_2408_);
                    leanh::lean_dec(v_s_2407_);
                    v___x_2425_ = leanh::lean_box(0);
                    v_isShared_2426_ = v_isSharedCheck_2431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2427_, 0, v_one_2406_);
                if v_isShared_2426_ == 0 {
                    leanh::lean_ctor_set(v___x_2425_, 13, v___x_2427_);
                    v___x_2429_ = v___x_2425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2430_ = leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_id_2408_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_type_2409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 2, v_u_2410_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 3, v_ringInst_2411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 4, v_semiringInst_2412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 5, v_charInst_x3f_2413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 6, v_addFn_x3f_2414_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 7, v_mulFn_x3f_2415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 8, v_subFn_x3f_2416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 9, v_negFn_x3f_2417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 10, v_powFn_x3f_2418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 11, v_intCastFn_x3f_2419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 12, v_natCastFn_x3f_2420_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 13, v___x_2427_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 14, v_vars_2421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 15, v_varMap_2422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2430_, 16, v_denote_2423_);
                    v___x_2429_ = v_reuseFailAlloc_2430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1(
    mut v_toPure_2433_: *mut leanh::LeanObject,
    mut v_one_2434_: *mut leanh::LeanObject,
    mut v_____r_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2436_ =
        leanh::lean_apply_2(v_toPure_2433_, leanh::lean_box(0), v_one_2434_);
    return v___x_2436_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2(
    mut v_one_2437_: *mut leanh::LeanObject,
    mut v_inst_2438_: *mut leanh::LeanObject,
    mut v_toBind_2439_: *mut leanh::LeanObject,
    mut v___f_2440_: *mut leanh::LeanObject,
    mut v_____r_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = leanh::lean_unsigned_to_nat(0);
    v___x_2443_ = leanh::lean_box(0);
    v___x_2444_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_internalize___boxed as *mut core::ffi::c_void,
        14,
        3,
    );
    leanh::lean_closure_set(v___x_2444_, 0, v_one_2437_);
    leanh::lean_closure_set(v___x_2444_, 1, v___x_2442_);
    leanh::lean_closure_set(v___x_2444_, 2, v___x_2443_);
    v___x_2445_ = leanh::lean_apply_2(v_inst_2438_, leanh::lean_box(0), v___x_2444_);
    v___x_2446_ = leanh::lean_apply_4(
        v_toBind_2439_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2445_,
        v___f_2440_,
    );
    return v___x_2446_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3(
    mut v_toPure_2447_: *mut leanh::LeanObject,
    mut v_inst_2448_: *mut leanh::LeanObject,
    mut v_toBind_2449_: *mut leanh::LeanObject,
    mut v_modifyRing_2450_: *mut leanh::LeanObject,
    mut v_one_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_one_2451_, 2);
    v___f_2452_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2452_, 0, v_one_2451_);
    v___f_2453_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2453_, 0, v_toPure_2447_);
    leanh::lean_closure_set(v___f_2453_, 1, v_one_2451_);
    leanh::lean_inc(v_toBind_2449_);
    v___f_2454_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2454_, 0, v_one_2451_);
    leanh::lean_closure_set(v___f_2454_, 1, v_inst_2448_);
    leanh::lean_closure_set(v___f_2454_, 2, v_toBind_2449_);
    leanh::lean_closure_set(v___f_2454_, 3, v___f_2453_);
    v___x_2455_ = leanh::lean_apply_1(v_modifyRing_2450_, v___f_2452_);
    v___x_2456_ = leanh::lean_apply_4(
        v_toBind_2449_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2455_,
        v___f_2454_,
    );
    return v___x_2456_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4(
    mut v_toPure_2457_: *mut leanh::LeanObject,
    mut v_inst_2458_: *mut leanh::LeanObject,
    mut v_toBind_2459_: *mut leanh::LeanObject,
    mut v___f_2460_: *mut leanh::LeanObject,
    mut v_ring_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_one_x3f_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_one_x3f_2462_ = leanh::lean_ctor_get(v_ring_2461_, 13);
    if leanh::lean_obj_tag(v_one_x3f_2462_) == 1 {
        let mut v_val_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_one_x3f_2462_);
        leanh::lean_dec_ref(v_ring_2461_);
        leanh::lean_dec(v___f_2460_);
        leanh::lean_dec(v_toBind_2459_);
        leanh::lean_dec_ref(v_inst_2458_);
        v_val_2463_ = leanh::lean_ctor_get(v_one_x3f_2462_, 0);
        leanh::lean_inc(v_val_2463_);
        leanh::lean_dec_ref_known(v_one_x3f_2462_, 1);
        v___x_2464_ =
            leanh::lean_apply_2(v_toPure_2457_, leanh::lean_box(0), v_val_2463_);
        return v___x_2464_;
    } else {
        let mut v_type_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_u_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_semiringInst_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2457_);
        v_type_2465_ = leanh::lean_ctor_get(v_ring_2461_, 1);
        leanh::lean_inc_ref(v_type_2465_);
        v_u_2466_ = leanh::lean_ctor_get(v_ring_2461_, 2);
        leanh::lean_inc(v_u_2466_);
        v_semiringInst_2467_ = leanh::lean_ctor_get(v_ring_2461_, 4);
        leanh::lean_inc_ref(v_semiringInst_2467_);
        leanh::lean_dec_ref(v_ring_2461_);
        v___x_2468_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions_0__Lean_Meta_Grind_Arith_CommRing_mkOne___redArg(v_inst_2458_, v_u_2466_, v_type_2465_, v_semiringInst_2467_);
        v___x_2469_ = leanh::lean_apply_4(
            v_toBind_2459_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2468_,
            v___f_2460_,
        );
        return v___x_2469_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(
    mut v_inst_2470_: *mut leanh::LeanObject,
    mut v_inst_2471_: *mut leanh::LeanObject,
    mut v_inst_2472_: *mut leanh::LeanObject,
    mut v_inst_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getRing_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyRing_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2474_ = leanh::lean_ctor_get(v_inst_2470_, 0);
    leanh::lean_inc_ref(v_toApplicative_2474_);
    v_toBind_2475_ = leanh::lean_ctor_get(v_inst_2470_, 1);
    leanh::lean_inc_n(v_toBind_2475_, 3);
    leanh::lean_dec_ref(v_inst_2470_);
    v_getRing_2476_ = leanh::lean_ctor_get(v_inst_2472_, 0);
    leanh::lean_inc(v_getRing_2476_);
    v_modifyRing_2477_ = leanh::lean_ctor_get(v_inst_2472_, 1);
    leanh::lean_inc(v_modifyRing_2477_);
    leanh::lean_dec_ref(v_inst_2472_);
    v_toPure_2478_ = leanh::lean_ctor_get(v_toApplicative_2474_, 1);
    leanh::lean_inc_n(v_toPure_2478_, 2);
    leanh::lean_dec_ref(v_toApplicative_2474_);
    v___f_2479_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2479_, 0, v_toPure_2478_);
    leanh::lean_closure_set(v___f_2479_, 1, v_inst_2473_);
    leanh::lean_closure_set(v___f_2479_, 2, v_toBind_2475_);
    leanh::lean_closure_set(v___f_2479_, 3, v_modifyRing_2477_);
    v___f_2480_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2480_, 0, v_toPure_2478_);
    leanh::lean_closure_set(v___f_2480_, 1, v_inst_2471_);
    leanh::lean_closure_set(v___f_2480_, 2, v_toBind_2475_);
    leanh::lean_closure_set(v___f_2480_, 3, v___f_2479_);
    v___x_2481_ = leanh::lean_apply_4(
        v_toBind_2475_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getRing_2476_,
        v___f_2480_,
    );
    return v___x_2481_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getOne(
    mut v_m_2482_: *mut leanh::LeanObject,
    mut v_inst_2483_: *mut leanh::LeanObject,
    mut v_inst_2484_: *mut leanh::LeanObject,
    mut v_inst_2485_: *mut leanh::LeanObject,
    mut v_inst_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = l_Lean_Meta_Grind_Arith_CommRing_getOne___redArg(
        v_inst_2483_,
        v_inst_2484_,
        v_inst_2485_,
        v_inst_2486_,
    );
    return v___x_2487_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0(
    mut v_invFn_2488_: *mut leanh::LeanObject,
    mut v_s_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toRing_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2503_: u8 = 0;
    let mut v_invSet_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2507_: u8 = 0;
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2510_: u8 = 0;
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2515_: u8 = 0;
    let mut v_unused_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2490_ = leanh::lean_ctor_get(v_s_2489_, 0);
                v_semiringId_x3f_2491_ = leanh::lean_ctor_get(v_s_2489_, 2);
                v_commSemiringInst_2492_ = leanh::lean_ctor_get(v_s_2489_, 3);
                v_commRingInst_2493_ = leanh::lean_ctor_get(v_s_2489_, 4);
                v_noZeroDivInst_x3f_2494_ = leanh::lean_ctor_get(v_s_2489_, 5);
                v_fieldInst_x3f_2495_ = leanh::lean_ctor_get(v_s_2489_, 6);
                v_powIdentityInst_x3f_2496_ = leanh::lean_ctor_get(v_s_2489_, 7);
                v_denoteEntries_2497_ = leanh::lean_ctor_get(v_s_2489_, 8);
                v_nextId_2498_ = leanh::lean_ctor_get(v_s_2489_, 9);
                v_steps_2499_ = leanh::lean_ctor_get(v_s_2489_, 10);
                v_queue_2500_ = leanh::lean_ctor_get(v_s_2489_, 11);
                v_basis_2501_ = leanh::lean_ctor_get(v_s_2489_, 12);
                v_diseqs_2502_ = leanh::lean_ctor_get(v_s_2489_, 13);
                v_recheck_2503_ = leanh::lean_ctor_get_uint8(
                    v_s_2489_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2504_ = leanh::lean_ctor_get(v_s_2489_, 14);
                v_powIdentityVarCount_2505_ = leanh::lean_ctor_get(v_s_2489_, 15);
                v_numEq0_x3f_2506_ = leanh::lean_ctor_get(v_s_2489_, 16);
                v_numEq0Updated_2507_ = leanh::lean_ctor_get_uint8(
                    v_s_2489_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2515_ = (!leanh::lean_is_exclusive(v_s_2489_)) as u8;
                if v_isSharedCheck_2515_ == 0 {
                    v_unused_2516_ = leanh::lean_ctor_get(v_s_2489_, 1);
                    leanh::lean_dec(v_unused_2516_);
                    v___x_2509_ = v_s_2489_;
                    v_isShared_2510_ = v_isSharedCheck_2515_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_numEq0_x3f_2506_);
                    leanh::lean_inc(v_powIdentityVarCount_2505_);
                    leanh::lean_inc(v_invSet_2504_);
                    leanh::lean_inc(v_diseqs_2502_);
                    leanh::lean_inc(v_basis_2501_);
                    leanh::lean_inc(v_queue_2500_);
                    leanh::lean_inc(v_steps_2499_);
                    leanh::lean_inc(v_nextId_2498_);
                    leanh::lean_inc(v_denoteEntries_2497_);
                    leanh::lean_inc(v_powIdentityInst_x3f_2496_);
                    leanh::lean_inc(v_fieldInst_x3f_2495_);
                    leanh::lean_inc(v_noZeroDivInst_x3f_2494_);
                    leanh::lean_inc(v_commRingInst_2493_);
                    leanh::lean_inc(v_commSemiringInst_2492_);
                    leanh::lean_inc(v_semiringId_x3f_2491_);
                    leanh::lean_inc(v_toRing_2490_);
                    leanh::lean_dec(v_s_2489_);
                    v___x_2509_ = leanh::lean_box(0);
                    v_isShared_2510_ = v_isSharedCheck_2515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2511_, 0, v_invFn_2488_);
                if v_isShared_2510_ == 0 {
                    leanh::lean_ctor_set(v___x_2509_, 1, v___x_2511_);
                    v___x_2513_ = v___x_2509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_toRing_2490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 1, v___x_2511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_semiringId_x3f_2491_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        3,
                        v_commSemiringInst_2492_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_commRingInst_2493_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        5,
                        v_noZeroDivInst_x3f_2494_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 6, v_fieldInst_x3f_2495_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        7,
                        v_powIdentityInst_x3f_2496_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 8, v_denoteEntries_2497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 9, v_nextId_2498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 10, v_steps_2499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 11, v_queue_2500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 12, v_basis_2501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 13, v_diseqs_2502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 14, v_invSet_2504_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2514_,
                        15,
                        v_powIdentityVarCount_2505_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 16, v_numEq0_x3f_2506_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2514_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_2503_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2514_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2507_,
                    );
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1(
    mut v_toPure_2517_: *mut leanh::LeanObject,
    mut v_invFn_2518_: *mut leanh::LeanObject,
    mut v_____r_2519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2520_ =
        leanh::lean_apply_2(v_toPure_2517_, leanh::lean_box(0), v_invFn_2518_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2(
    mut v_toPure_2521_: *mut leanh::LeanObject,
    mut v_modifyCommRing_2522_: *mut leanh::LeanObject,
    mut v_toBind_2523_: *mut leanh::LeanObject,
    mut v_invFn_2524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_invFn_2524_);
    v___f_2525_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2525_, 0, v_invFn_2524_);
    v___f_2526_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2526_, 0, v_toPure_2521_);
    leanh::lean_closure_set(v___f_2526_, 1, v_invFn_2524_);
    v___x_2527_ = leanh::lean_apply_1(v_modifyCommRing_2522_, v___f_2525_);
    v___x_2528_ = leanh::lean_apply_4(
        v_toBind_2523_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2527_,
        v___f_2526_,
    );
    return v___x_2528_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__7;
    v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
    return v___x_2545_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3(
    mut v_toPure_2546_: *mut leanh::LeanObject,
    mut v_inst_2547_: *mut leanh::LeanObject,
    mut v_inst_2548_: *mut leanh::LeanObject,
    mut v_inst_2549_: *mut leanh::LeanObject,
    mut v_inst_2550_: *mut leanh::LeanObject,
    mut v_toBind_2551_: *mut leanh::LeanObject,
    mut v___f_2552_: *mut leanh::LeanObject,
    mut v_ring_2553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fieldInst_x3f_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fieldInst_x3f_2554_ = leanh::lean_ctor_get(v_ring_2553_, 6);
    if leanh::lean_obj_tag(v_fieldInst_x3f_2554_) == 1 {
        let mut v_invFn_x3f_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_fieldInst_x3f_2554_);
        v_invFn_x3f_2555_ = leanh::lean_ctor_get(v_ring_2553_, 1);
        if leanh::lean_obj_tag(v_invFn_x3f_2555_) == 1 {
            let mut v_val_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_invFn_x3f_2555_);
            leanh::lean_dec_ref_known(v_fieldInst_x3f_2554_, 1);
            leanh::lean_dec_ref(v_ring_2553_);
            leanh::lean_dec(v___f_2552_);
            leanh::lean_dec(v_toBind_2551_);
            leanh::lean_dec_ref(v_inst_2550_);
            leanh::lean_dec_ref(v_inst_2549_);
            leanh::lean_dec_ref(v_inst_2548_);
            leanh::lean_dec(v_inst_2547_);
            v_val_2556_ = leanh::lean_ctor_get(v_invFn_x3f_2555_, 0);
            leanh::lean_inc(v_val_2556_);
            leanh::lean_dec_ref_known(v_invFn_x3f_2555_, 1);
            v___x_2557_ =
                leanh::lean_apply_2(v_toPure_2546_, leanh::lean_box(0), v_val_2556_);
            return v___x_2557_;
        } else {
            let mut v_toRing_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_u_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_expectedInst_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_2546_);
            v_toRing_2558_ = leanh::lean_ctor_get(v_ring_2553_, 0);
            leanh::lean_inc_ref(v_toRing_2558_);
            leanh::lean_dec_ref(v_ring_2553_);
            v_val_2559_ = leanh::lean_ctor_get(v_fieldInst_x3f_2554_, 0);
            leanh::lean_inc(v_val_2559_);
            leanh::lean_dec_ref_known(v_fieldInst_x3f_2554_, 1);
            v_type_2560_ = leanh::lean_ctor_get(v_toRing_2558_, 1);
            leanh::lean_inc_ref_n(v_type_2560_, 2);
            v_u_2561_ = leanh::lean_ctor_get(v_toRing_2558_, 2);
            leanh::lean_inc_n(v_u_2561_, 2);
            leanh::lean_dec_ref(v_toRing_2558_);
            v___x_2562_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__2;
            v___x_2563_ = leanh::lean_box(0);
            v___x_2564_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2564_, 0, v_u_2561_);
            leanh::lean_ctor_set(v___x_2564_, 1, v___x_2563_);
            v___x_2565_ = l_Lean_mkConst(v___x_2562_, v___x_2564_);
            v_expectedInst_2566_ = l_Lean_mkAppB(v___x_2565_, v_type_2560_, v_val_2559_);
            v___x_2567_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__4;
            v___x_2568_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__6;
            v___x_2569_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___redArg(
                v_inst_2547_,
                v_inst_2548_,
                v_inst_2549_,
                v_inst_2550_,
                v_type_2560_,
                v_u_2561_,
                v___x_2567_,
                v___x_2568_,
                v_expectedInst_2566_,
            );
            v___x_2570_ = leanh::lean_apply_4(
                v_toBind_2551_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2569_,
                v___f_2552_,
            );
            return v___x_2570_;
        }
    } else {
        let mut v_toRing_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2552_);
        leanh::lean_dec(v_toBind_2551_);
        leanh::lean_dec_ref(v_inst_2550_);
        leanh::lean_dec(v_inst_2547_);
        leanh::lean_dec(v_toPure_2546_);
        v_toRing_2571_ = leanh::lean_ctor_get(v_ring_2553_, 0);
        leanh::lean_inc_ref(v_toRing_2571_);
        leanh::lean_dec_ref(v_ring_2553_);
        v_type_2572_ = leanh::lean_ctor_get(v_toRing_2571_, 1);
        leanh::lean_inc_ref(v_type_2572_);
        leanh::lean_dec_ref(v_toRing_2571_);
        v___x_2573_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8
            ),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8_once
            ),
            _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3___closed__8,
        );
        v___x_2574_ = l_Lean_indentExpr(v_type_2572_);
        v___x_2575_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2575_, 0, v___x_2573_);
        leanh::lean_ctor_set(v___x_2575_, 1, v___x_2574_);
        v___x_2576_ = l_Lean_throwError___redArg(v_inst_2549_, v_inst_2548_, v___x_2575_);
        return v___x_2576_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(
    mut v_inst_2577_: *mut leanh::LeanObject,
    mut v_inst_2578_: *mut leanh::LeanObject,
    mut v_inst_2579_: *mut leanh::LeanObject,
    mut v_inst_2580_: *mut leanh::LeanObject,
    mut v_inst_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getCommRing_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyCommRing_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2582_ = leanh::lean_ctor_get(v_inst_2579_, 0);
    v_toBind_2583_ = leanh::lean_ctor_get(v_inst_2579_, 1);
    leanh::lean_inc_n(v_toBind_2583_, 3);
    v_getCommRing_2584_ = leanh::lean_ctor_get(v_inst_2581_, 0);
    leanh::lean_inc(v_getCommRing_2584_);
    v_modifyCommRing_2585_ = leanh::lean_ctor_get(v_inst_2581_, 1);
    leanh::lean_inc(v_modifyCommRing_2585_);
    leanh::lean_dec_ref(v_inst_2581_);
    v_toPure_2586_ = leanh::lean_ctor_get(v_toApplicative_2582_, 1);
    leanh::lean_inc_n(v_toPure_2586_, 2);
    v___f_2587_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2587_, 0, v_toPure_2586_);
    leanh::lean_closure_set(v___f_2587_, 1, v_modifyCommRing_2585_);
    leanh::lean_closure_set(v___f_2587_, 2, v_toBind_2583_);
    v___f_2588_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2588_, 0, v_toPure_2586_);
    leanh::lean_closure_set(v___f_2588_, 1, v_inst_2577_);
    leanh::lean_closure_set(v___f_2588_, 2, v_inst_2578_);
    leanh::lean_closure_set(v___f_2588_, 3, v_inst_2579_);
    leanh::lean_closure_set(v___f_2588_, 4, v_inst_2580_);
    leanh::lean_closure_set(v___f_2588_, 5, v_toBind_2583_);
    leanh::lean_closure_set(v___f_2588_, 6, v___f_2587_);
    v___x_2589_ = leanh::lean_apply_4(
        v_toBind_2583_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getCommRing_2584_,
        v___f_2588_,
    );
    return v___x_2589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getInvFn(
    mut v_m_2590_: *mut leanh::LeanObject,
    mut v_inst_2591_: *mut leanh::LeanObject,
    mut v_inst_2592_: *mut leanh::LeanObject,
    mut v_inst_2593_: *mut leanh::LeanObject,
    mut v_inst_2594_: *mut leanh::LeanObject,
    mut v_inst_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2596_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___redArg(
        v_inst_2591_,
        v_inst_2592_,
        v_inst_2593_,
        v_inst_2594_,
        v_inst_2595_,
    );
    return v___x_2596_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Functions(builtin);
}